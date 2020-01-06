#include "Term.hpp"
#include "souffle/CompiledSouffle.h"
#include "Symbol.hpp"

using namespace flg;
using namespace souffle;
using namespace std;

template <class T, size_t N>
ostream& operator<<(ostream& out, const array<T, N>& arr)
{
  out << "[";
  for (size_t i = 0; i < N; ++i) {
    out << arr[i];
    if (i < N - 1) {
      out << ", ";
    }
  }
  out << "]";
  return out;
}

// Define tuples, comparators, and relations
/* INSERT 0 */

void loadEdbs() {
/* INSERT 1 */
}

void printRelations() {
/* INSERT 2 */
}

int main() {
  loadEdbs();
  printRelations();
  return 0;
}
