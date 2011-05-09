#ifndef __AMALLOC_H_
#define __AMALLOC_H_
#include <stdlib.h>

static inline void * amalloc (size_t s) {
	void * ret;
	ret = malloc (s);
	if (!ret)
		abort();
	return ret;
};

static inline void * acalloc (size_t n, size_t s) {
	void * ret;
	ret = calloc (n, s);
	if (!ret)
		abort();
	return ret;
};

#endif /* __AMALLOC_H_ */
