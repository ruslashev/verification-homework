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

/*@ axiomatic NumLess {
      logic int num_less{L}(int *a, integer l, integer h, integer x);
      axiom num_less_invalid{L}:
        \forall int* a, integer l, h, x;
          0 <= l && h <= l ==> num_less(a, l, h, x) == 0;
      axiom num_less_next{L}:
        \forall int *a, integer l, h, x;
          0 <= l <= h ==> num_less(a, l, h, x) == num_less(a, l, h - 1, x) + (a[h - 1] < x ? 1 : 0);
    }
@*/

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
            loop invariant idx == lo + num_less(arr, lo + 1, i, x);
            loop invariant 0 <= idx - lo <= i;
            loop assigns idx;
            loop variant i;
         */
        for (i = lo + 1; i < n; ++i)
            if (arr[i] < x)
                ++idx;

        /*@ assert idx >= lo; */

        if (idx == lo) {
            /*@ assert sorted(arr, 0, idx); */
            continue;
        }

        /*@ assert idx > lo; */

        /*@ loop invariant lo < idx;
            loop invariant \forall integer i; lo <= i < idx ==> arr[i] == x;
            loop variant idx;
         */
        while (x == arr[idx]) {
            /*@ assert arr[idx] == arr[idx - 1]; */
            ++idx;
        }

        /*@ assert idx > lo; */

        if (idx != lo) {
            swap(tmp, x, arr[idx]);
            /*@ assert sorted(arr, idx, idx); */
        }

        /*@ assert idx > lo; */

        /*@ loop invariant lo < idx;
            loop assigns idx, i, tmp, arr[lo .. n - 2], x;
            loop variant idx;
          */
        while (idx != lo) {
            idx = lo;

            /*@ loop invariant lo < i <= n;
                loop invariant idx == lo + num_less(arr, lo + 1, i, x);
                loop invariant 0 <= idx - lo <= i;
                loop assigns idx;
                loop variant i;
             */
            for (i = lo + 1; i < n; ++i)
                if (arr[i] < x)
                    ++idx;

            /*@ assert idx >= lo; */

            /*@ loop invariant lo <= idx;
                loop invariant \forall integer i; lo <= i <= idx ==> arr[i] == x;
                loop variant idx;
              */
            while (x == arr[idx]) {
                /* TODO work on this vvv */
                /*@ assert arr[idx] == arr[idx - 1]; */
                ++idx;
            }

            /*@ assert idx >= lo; */

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

