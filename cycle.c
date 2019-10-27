#define swap(t, x, y) \
    { \
        t = x; \
        x = y; \
        y = t; \
    }

/*@ requires n > 0;
    requires \valid(arr + (0 .. n - 1));
    assigns arr[0 .. n - 1];

    ensures sorted(arr, 0, n - 1);
*/
static void cycle_lr(int *arr, int n)
{
    int lo, idx, x, i, tmp;

    for (lo = 0; lo < n - 1; ++lo) {
        x = arr[lo];
        idx = lo;

        for (i = lo + 1; i < n; ++i)
            if (arr[i] < x)
                ++idx;

        if (idx == lo)
            continue;

        while (x == arr[idx])
            ++idx;

        if (idx != lo)
            swap(tmp, x, arr[idx]);

        while (idx != lo) {
            idx = lo;

            for (i = lo + 1; i < n; ++i)
                if (arr[i] < x)
                    ++idx;

            while (x == arr[idx])
                ++idx;

            if (x != arr[idx])
                swap(tmp, x, arr[idx]);
        }
    }
}

