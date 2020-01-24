#include <boost/asio.hpp>
#include <boost/filesystem.hpp>

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
  boost::asio::post(pool,
      [&]() {
        boost::filesystem::path path{dir};
        path /= file;
        FactParser<T> parser;
        parser.parse(path.string(), rel);
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

void printResults() {
/* INSERT 4 */
}

int main() {
  loadEdbs({}, 1);
  evaluate();
  printResults();
  return 0;
}
