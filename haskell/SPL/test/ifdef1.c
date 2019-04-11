#ifdef A
#define X 1
#else
#define X 2
#endif
#ifdef B
#define Y 3
#else
#ifdef C
#define Y 4
#else
#define Y 5
#endif
#endif
int main() {return Y + X;}
