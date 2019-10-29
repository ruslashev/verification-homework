#include <limits.h>

#define swap(t, x, y) \
    { \
        t = x; \
        x = y; \
        y = t; \
    }

/*@ predicate sorted{L}(int *arr, integer l, integer h) =
      \forall integer i, j; l <= i <= j <= h ==> arr[i] <= arr[j];

    predicate sorted{L}(int *a, integer n) = sorted{L}(a, 0, n - 1);
*/

/*@ requires 0 < n < INT_MAX;
    requires \valid(arr + (0 .. n - 1));
    assigns arr[0 .. n - 1];
    ensures sorted(arr, n);
*/
static void cycle_lr(int *arr, int n)
{
    int lo, idx, x, i, tmp;

    /*@ loop invariant 0 <= lo < n;
        loop invariant sorted(arr, 0, lo);
        loop assigns i, tmp, x, idx, arr[0 .. n - 2];
        loop variant lo;
     */
    for (lo = 0; lo < n - 1; ++lo) {
        x = arr[lo];
        idx = lo;

        /*@ loop invariant lo < i <= n;
            loop invariant idx == lo + num_less_than
            loop invariant idx == lo + num_less_than;
            loop invariant lo <= idx <= lo + num_less_than;
            loop assigns idx;
            loop variant i;
         */
        for (i = lo + 1; i < n; ++i)
            /*@ ghost if (arr[i] < x) ++num_less_than; */
            if (arr[i] < x)
                ++idx;

        if (idx == lo) {
            /*@ assert sorted(arr, 0, idx); */
            continue;
        }

        /*@ ghost WhBegOut:; */
        /*@ loop invariant lo < idx;
            loop variant idx;
         */
        while (x == arr[idx]) {
            /* assert arr[idx] == arr[\at(idx,WhBegOut)]; */
            ++idx;
        }
        /*@ assert \forall integer i; lo <= i < idx ==> arr[lo] == arr[i]; */

        if (idx != lo) {
            swap(tmp, x, arr[idx]);
            /*@ assert sorted(arr, idx, idx); */
        }

        /*@ ghost int old_idx = idx; */
        /*@ loop invariant lo <= idx < n;
            loop assigns idx, tmp, arr[idx], x;
            loop variant idx;
          */
        while (idx != lo) {
            idx = lo;

            /*@ ghost int num_less_than_c = 0; */
            /*@ loop invariant lo < i <= n;
                loop invariant lo <= idx;
                loop invariant idx == lo + num_less_than_c;
                loop assigns idx;
                loop variant i;
             */
            for (i = lo + 1; i < n; ++i)
                /*@ ghost if (arr[i] < x) ++num_less_than_c; */
                if (arr[i] < x)
                    ++idx;

            /*@ loop variant idx;
             */
            while (x == arr[idx])
                ++idx;

            if (x != arr[idx]) {
                swap(tmp, x, arr[idx]);
                /*@ assert sorted(arr, idx, idx); */
            }
        }
        /*@ assert idx == lo; */
        /*@ assert sorted(arr, 0, lo); */
    }

    /*@ assert sorted(arr, 0, n - 1); */
}

