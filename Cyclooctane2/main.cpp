#include "cyclooctane2.h"
int main()
{
	initi();
	while(1)
		FSM::current->eventt();
	return 0;
}