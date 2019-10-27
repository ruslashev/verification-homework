/*@ requires n >= 0;
    requires \valid(arr + (0 .. n - 1));
    assigns \nothing;

    ensures \forall integer i, integer j;
        0 <= i < j < n ==> arr[i] <= arr[j];
*/
static void cycle_lr(int *arr, int n)
{
    int lo, idx, x, i, tmp;

    for (lo = 0; lo <= n - 2; lo++) {
        x = arr[lo];
        idx = lo;

        for (i = lo + 1; i < n; i++) {
            if (arr[i] < x) {
                idx++;
            }
        }

        if (idx == lo) {
            continue;
        }

        while (x == arr[idx]) {
            idx += 1;
        }

        if (idx != lo) {
            tmp = arr[idx];
            arr[idx] = x;
            x = tmp;
        }

        while (idx != lo) {
            idx = lo;

            for (i = lo + 1; i < n; i++) {
                if (arr[i] < x) {
                    idx += 1;
                }
            }

            while (x == arr[idx]) {
                idx += 1;
            }

            if (x != arr[idx]) {
                tmp = arr[idx];
                arr[idx] = x;
                x = tmp;
            }
        }
    }
}

