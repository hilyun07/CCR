#ifndef VECTOR_H_
#define VECTOR_H_

#include <stddef.h>

typedef struct vector {
  void *data;
  size_t esize;
  size_t capacity;
  size_t length;
} vector;

// typedef struct slice {
//   void *data;
//   size_t esize;
//   size_t length;
// } slice;

/* inititlizer and destructor */
void vector_init(vector *v, size_t esize, size_t capacity);
void vector_destruct(vector *v);

/* field access */
size_t vector_esize(const vector *v);
size_t vector_capacity(const vector *v);
size_t vector_length(const vector *v);

/* adjusting capacity */
void vector_reserve(vector *v, size_t min_capacity);
// void vector_shrink(vector *v, size_t min_capacity);

/* modifying elements */
void vector_push(vector *v, const void *src);
// void vector_pop(vector *v, void *dst);
void vector_get(const vector *v, size_t index, void *dst);
void vector_set(const vector *v, size_t index, const void *src);
void vector_remove(vector *v, size_t index);

/* direct access */
// void *vector_data(const vector *v);
// void *vector_get_ptr(const vector *v, size_t index);
// slice vector_get_slice(const vector *v, size_t index, size_t length);

#endif
