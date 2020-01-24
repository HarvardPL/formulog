#include "funcs.hpp"
// FactParser.hpp needs to be included *after* everything else. It pulls in
// some Antlr headers that unset the EOF macro, which Souffle depends on.
#include "FactParser.hpp"

using namespace flg;
using namespace std;

void loadEdbs() {
/* INSERT 0 */
}

/* INSERT 1 */

void evaluate() {
/* INSERT 2 */
}

void printResults() {
/* INSERT 3 */
}

int main() {
  loadEdbs();
  evaluate();
  printResults();
  return 0;
}
