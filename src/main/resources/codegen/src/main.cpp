#include <fstream>
#include <iostream>
#include <vector>
#include <string>

#include <boost/asio.hpp>
#include <boost/filesystem.hpp>
#include <boost/program_options.hpp>
#include <omp.h>

#include "parser.hpp"
#include "functors.h"
#include "globals.h"

using namespace flg;
using namespace std;

struct ExternalEdbLoader {
    ExternalEdbLoader(size_t nthreads) : pool(nthreads) {}

    void go(const vector<string> &dirs);

private:
    boost::asio::thread_pool pool;

    void loadEdbs(const string &dir);

    void loadEdbs(const string &dir, const string &file, souffle::Relation *rel);
};

void ExternalEdbLoader::go(const vector<string> &dirs) {
    for (auto &dir: dirs) {
        loadEdbs(dir);
    }
    pool.join();
}

void ExternalEdbLoader::loadEdbs(const string &dir) {
/* INSERT 0 */
}

void ExternalEdbLoader::loadEdbs(const string &dir, const string &file, souffle::Relation *rel) {
    assert(rel);
    boost::filesystem::path path{dir};
    path /= file;
    string pathstr = path.string();
    boost::asio::post(pool, [pathstr, rel]() {
        ifstream stream(pathstr);
        parse_facts(stream, *rel);
    });
}

void loadFact(const string &relname, vector<term_ptr> args) {
    auto rel = globals::program->getRelation(relname);
    assert(rel);
    souffle::tuple tup(rel);
    for (auto arg: args) {
        tup << arg->intize();
    }
    rel->insert(tup);
}

void loadEdbs(const vector<string> &dirs, size_t nthreads) {
    ExternalEdbLoader(nthreads).go(dirs);
/* INSERT 1 */
}

/* INSERT 2 */

void evaluate() {
/* INSERT 3 */
}

void printResults(bool dump) {
    for (auto rel: globals::program->getOutputRelations()) {
        std::string name = rel->getName();
        if (name.find("CODEGEN_") == 0) {
            continue;
        }
        name = name.substr(0, name.size() - 1);
        std::cout << name << ": " << rel->size() << std::endl;
        if (dump) {
            for (auto &tup: *rel) {
                std::cout << name << "(";
                for (size_t i = 0; i < rel->getPrimaryArity(); ++i) {
                    std::cout << *Term::unintize(tup[i]);
                    if (i < rel->getPrimaryArity() - 1) {
                        std::cout << ", ";
                    }
                }
                std::cout << ")" << std::endl;
            }
        }
    }
}

namespace std {
std::ostream &operator<<(std::ostream &os, const std::vector<std::string> &vec) {
    for (auto item: vec) {
        os << item << " ";
    }
    return os;
}
}

int main(int argc, char **argv) {
    namespace po = boost::program_options;
    po::options_description desc("Allowed options");
    string cwd = boost::filesystem::current_path().string();
    desc.add_options()
            ("help", "produce help message")
            ("parallelism,j", po::value<size_t>()->default_value(1),
             "number of threads to use")
            ("no-dump", "only print sizes of relations, not the database")
            ("fact-dir", po::value<vector<string>>()->default_value({cwd}),
             "input directory with external EDBs (can be set multiple times)")
            ("smt-solver-mode", po::value<smt::SmtSolverMode>()->default_value(smt::SmtSolverMode::check_sat_assuming),
             "set interaction strategy between Formulog and the external SMT solver")
            ("smt-double-check", po::value<bool>()->default_value(true),
             "double check unknown values returned by SMT solver (using a generally more reliable solver mode)");

    po::variables_map vm;
    po::store(po::parse_command_line(argc, argv, desc), vm);
    po::notify(vm);

    if (vm.count("help")) {
        cout << desc << endl;
        return 1;
    }

    size_t parallelism = vm["parallelism"].as<size_t>();
    if (parallelism == 0) {
        cout << "Cannot use 0 threads" << endl;
        return 1;
    }

    initialize_symbols();
    globals::smt_solver_mode = vm["smt-solver-mode"].as<smt::SmtSolverMode>();
    globals::smt_double_check = vm["smt-double-check"].as<bool>();
    globals::program = souffle::ProgramFactory::newInstance("formulog");
    if (!globals::program) {
        cout << "Unable to load Souffle program" << endl;
        exit(1);
    }
    loadEdbs(vm["fact-dir"].as<vector<string>>(), parallelism);
    globals::program->setNumThreads(parallelism);
    globals::program->run();
    // TODO create directory first
    // prog->printAll("souffle_out");
    printResults(!vm.count("no-dump"));
    return 0;
}
