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
        stream.close();
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

struct ExternalIdbPrinter {
    ExternalIdbPrinter(const boost::filesystem::path &dir_, size_t nthreads) : dir(dir_), pool(nthreads) {}

    void go();

private:
    const boost::filesystem::path dir;

    boost::asio::thread_pool pool;

    void saveToDisk(const string &name);
};

void ExternalIdbPrinter::saveToDisk(const string &name) {
    auto rel = globals::program->getRelation(name);
    assert(rel);
    auto path(dir);
    auto corrected_name = name.substr(0, name.size() - 1);
    path /= corrected_name;
    auto pathstr = path.string() + string(".tsv");
    boost::asio::post(pool, [pathstr, rel]() {
        ofstream ofs(pathstr);
        for (auto &tup: *rel) {
            for (size_t i = 0; i < rel->getPrimaryArity(); ++i) {
                ofs << *Term::unintize(tup[i]);
                if (i < rel->getPrimaryArity() - 1) {
                    ofs << "\t";
                }
            }
            ofs << "\n";
        }
        ofs.flush();
        ofs.close();
    });
}

void ExternalIdbPrinter::go() {
/* INSERT 4 */
    pool.join();
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
    bool dump_idb{false};
    bool no_smt_double_check{false};
    desc.add_options()
            ("help,h", "produce help message")
            ("parallelism,j", po::value<size_t>()->default_value(1),
             "number of threads to use")
            ("dump-idb", po::bool_switch(&dump_idb),
                    "print the contents of the IDB relations to screen")
            ("fact-dir,F", po::value<vector<string>>()->default_value({cwd}),
             "input directory with external EDBs (can be set multiple times)")
            ("out-dir,D", po::value<string>()->default_value(cwd),
             "directory for .tsv output files")
            ("smt-solver-mode", po::value<smt::SmtSolverMode>()->default_value(smt::SmtSolverMode::check_sat_assuming),
             "set interaction strategy between Formulog and the external SMT solver")
            ("no-smt-double-check", po::bool_switch(&no_smt_double_check),
             "do not double check unknown values returned by SMT solver (using a generally more reliable solver mode)")
            ("smt-cache-size", po::value<size_t>()->default_value(100),
             "how many implications to store for check-sat-assuming solver");

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
    globals::smt_double_check = !no_smt_double_check;
    globals::program = souffle::ProgramFactory::newInstance("formulog");
    if (!globals::program) {
        cout << "Unable to load Souffle program" << endl;
        exit(1);
    }
    loadEdbs(vm["fact-dir"].as<vector<string>>(), parallelism);
    globals::program->setNumThreads(parallelism);
    globals::program->run();
    flg::smt::SmtLibShim::terminate_all_children();
    boost::filesystem::path out_dir(vm["out-dir"].as<string>());
    boost::filesystem::create_directories(out_dir);
    ExternalIdbPrinter idbPrinter(out_dir, parallelism);
    idbPrinter.go();
    printResults(dump_idb);
    return 0;
}
