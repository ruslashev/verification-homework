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
    ensures sorted(arr, 0, n - 1);
*/
static void cycle_lr(int *arr, int n)
{
    int lo, idx, x, i, tmp;

    /*@ loop invariant 0 <= lo < n;
        loop invariant sorted(arr, 0, lo);
        loop assigns i, tmp, x, idx, arr[0 .. n - 2], lo;
        loop variant n - 1 - lo;
     */
    for (lo = 0; lo < n - 1; ++lo) {
        x = arr[lo];
        idx = lo;

        /*@ loop invariant lo < i <= n;
            loop invariant idx == lo + num_less(arr, lo + 1, i, x);
            loop invariant lo <= idx <= lo + i;
            loop invariant idx <= i <= n;
            loop assigns idx;
            loop variant i;
         */
        for (i = lo + 1; i < n; ++i)
            if (arr[i] < x)
                ++idx;

        /*@ assert lo <= idx <= n; */

        if (idx == lo) {
            /*@ assert sorted(arr, 0, lo); */
            /*@ assert \forall integer j; 0 <= j < lo ==> arr[j] <= arr[idx]; */
            /* assert \forall integer j; lo < j < n - 1 ==> arr[j] >= arr[idx]; */
            continue;
        }

        /*@ assert idx > lo; */

        /*@ ghost int old_idx = idx; */
        /*@ loop invariant lo < idx;
            loop invariant \forall integer j; old_idx <= j < idx ==> arr[j] == x;
            loop variant idx;
         */
        while (x == arr[idx])
            ++idx;

        /*@ assert idx > lo; */

        if (idx != lo) {
            swap(tmp, x, arr[idx]);
            /*@ assert sorted(arr, idx, idx); */
        }

        /*@ assert idx > lo; */

        /*@ loop invariant lo <= idx;
            loop assigns i, tmp, arr[lo .. n - 2], x;
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

            /*@ assert lo <= idx <= lo + n; */

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

