void e();

void f();

_Bool b();

void main() {
    int x = 1;

    while (x != 0) {
        if ((x == 1) && b()) {
            e();
            x = 2;
        }
        else if ((x == 2) && !b()) {
            f();
            x = 1;
        }
        else
            x = 0;
    }

    return;
}
