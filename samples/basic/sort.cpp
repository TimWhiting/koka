
#include <vector>
#include <algorithm>

int main() {
  auto v = std::vector<int>{};
  for (int i = 0; i < 100000000; ++i) {
    v.push_back(random());
  }
  std::sort(v.begin(), v.end());
  int sum = 0;
  for (auto i : v) {
    sum += i;
  }
  return sum;
}