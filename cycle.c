#include <limits.h>

#define swap(t, x, y) \
    { \
        t = x; \
        x = y; \
        y = t; \
    }

/*@ predicate sorted{L}(int *arr, integer l, integer h) =
      \forall integer i, j; l <= i <= j <= h ==> arr[i] <= arr[j];
*/

/*@ requires n > 0;
    requires \valid(arr + (0 .. n - 1));
    requires n < INT_MAX;
    assigns arr[0 .. n - 1];

    ensures sorted(arr, 0, n - 1);
*/
static void cycle_lr(int *arr, int n)
{
    int lo, idx, x, i, tmp;

    /*@ loop invariant 0 <= lo <= n - 1;
        loop assigns x, idx, i, tmp, arr[0..n - 2];
        loop variant lo;
     */
    for (lo = 0; lo < n - 1; ++lo) {
        x = arr[lo];
        idx = lo;

        /*@ loop invariant lo + 1 <= i <= n;
            loop invariant lo <= idx < n;
            loop assigns idx;
            loop variant i;
         */
        for (i = lo + 1; i < n; ++i)
            if (arr[i] < x)
                ++idx;

        if (idx == lo)
            continue;

        /*@ loop variant idx;
         */
        while (x == arr[idx])
            ++idx;

        if (idx != lo)
            swap(tmp, x, arr[idx]);

        /*@ loop assigns idx, tmp, arr, x;
            loop variant idx;
          */
        while (idx != lo) {
            idx = lo;

            /*@ loop invariant lo + 1 <= i <= n;
                loop assigns idx;
                loop variant i;
             */
            for (i = lo + 1; i < n; ++i)
                if (arr[i] < x)
                    ++idx;

            /*@ loop variant idx;
             */
            while (x == arr[idx])
                ++idx;

            if (x != arr[idx])
                swap(tmp, x, arr[idx]);
        }
    }
}

