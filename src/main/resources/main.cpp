#include <vector>
#include <string>

#include <boost/asio.hpp>
#include <boost/filesystem.hpp>
#include <boost/program_options.hpp>
#include <omp.h>

#include "FactParser.hpp"
#include "funcs.hpp"

using namespace flg;
using namespace std;

struct ExternalEdbLoader {
  ExternalEdbLoader(size_t nthreads) : pool(nthreads) {}

  void go(const vector<string>& dirs);

  private:
  boost::asio::thread_pool pool;

  void loadEdbs(const string& dir);
  template <typename T>
    void loadEdbs(const string& dir, const string& file, T& rel);
};

void ExternalEdbLoader::go(const vector<string>& dirs) {
  for (auto& dir : dirs) {
    loadEdbs(dir);
  }
  pool.join();
}

void ExternalEdbLoader::loadEdbs(const string& dir) {
/* INSERT 0 */
}

template <typename T>
void ExternalEdbLoader::loadEdbs(const string& dir, const string& file, T& rel) {
  boost::filesystem::path path{dir};
  path /= file;
  auto s = path.string();
  boost::asio::post(pool,
      [s, &rel]() {
        FactParser<T> parser;
        parser.parse(s, rel);
      });
}

void loadEdbs(const vector<string>& dirs, size_t nthreads) {
  {
    ExternalEdbLoader edb_loader(nthreads);
    edb_loader.go(dirs);
  }
/* INSERT 1 */
}

/* INSERT 2 */

void evaluate() {
/* INSERT 3 */
}

void printResults(bool dump) {
/* INSERT 4 */
}

int main(int argc, char** argv) {
  namespace po = boost::program_options;
  po::options_description desc("Allowed options");
  string cwd = boost::filesystem::current_path().string(); 
  desc.add_options()
    ("help", "produce help message")
    ("parallelism,j", po::value<size_t>()->default_value(1),
     "number of threads to use")
    ("fact-dir", po::value<vector<string>>()->default_value({ cwd }),
     "input directory with external EDBs (can be set multiple times)")
    ("no-dump", "only print sizes of relations, not the database");

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
  omp_set_num_threads(parallelism);
  loadEdbs(vm["fact-dir"].as<vector<string>>(), parallelism);
  evaluate();
  printResults(!vm.count("no-dump"));
  return 0;
}
