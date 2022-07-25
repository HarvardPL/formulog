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

using namespace flg;
using namespace std;

struct ExternalEdbLoader {
    ExternalEdbLoader(size_t nthreads) : pool(nthreads) {}

    void go(const vector<string> &dirs);

private:
    boost::asio::thread_pool pool;

    void loadEdbs(const string &dir);

    template<typename T>
    void loadEdbs(const string &dir, const string &file, T &rel);
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

template<typename T>
void ExternalEdbLoader::loadEdbs(const string &dir, const string &file, T &rel) {
    boost::filesystem::path path{dir};
    path /= file;
    string pathstr = path.string();
    boost::asio::post(pool, [pathstr, &rel]() {
        ifstream stream(pathstr);
        parse_facts(stream, rel);
    });
}

void loadEdbs(const vector<string> &dirs, size_t nthreads) {
    ExternalEdbLoader(nthreads).go(dirs);
/* INSERT 1 */
}

/* INSERT 2 */

void evaluate() {
/* INSERT 3 */
}

void printResults(const souffle::SouffleProgram &prog, bool dump) {
    for (auto rel: prog.getOutputRelations()) {
        std::string name = rel->getName();
        name = name.substr(0, name.size() - 1);
        std::cout << name << ": " << rel->size() << std::endl;
        if (dump) {
            for (auto &tup: *rel) {
                std::cout << name << "(";
                for (size_t i = 0; i < rel->getPrimaryArity(); ++i) {
                    std::cout << Term::unintize(tup[i]);
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
             "input directory with external EDBs (can be set multiple times)");

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
    //omp_set_num_threads(parallelism);
    loadEdbs(vm["fact-dir"].as<vector<string>>(), parallelism);
    //evaluate();
    auto prog = souffle::ProgramFactory::newInstance("formulog");
    if (!prog) {
        cout << "Unable to load Souffle program" << endl;
        exit(1);
    }
    prog->setNumThreads(parallelism);
    prog->run();
    // TODO create directory first
    // prog->printAll("souffle_out");
    printResults(*prog, !vm.count("no-dump"));
    return 0;
}
