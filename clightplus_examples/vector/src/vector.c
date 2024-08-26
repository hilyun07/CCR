#define NDEBUG // disable assert
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include "vector.h"

/* initializer and destructor */
void vector_init(vector *v, size_t esize, size_t capacity) {
  *v = (vector) {
    .data = malloc(esize * capacity),
    .esize = esize,
    .capacity = capacity,
    .length = 0
  };
}

void vector_destruct(vector *v) {
  assert(v->data != NULL);

  free(v->data);
  v->data = NULL;
}

/* field access */
size_t vector_esize(const vector *v) { return v->esize; }
size_t vector_capacity(const vector *v) { return v->capacity; }
size_t vector_length(const vector *v) { return v->length; }

/* adjusting capacity */
void vector_reserve(vector *v, size_t min_capacity) {
  if (min_capacity <= v->capacity)
    return;

  v->data = realloc(v->data, v->esize * min_capacity);
  v->capacity = min_capacity;
}

// void vector_shrink(vector *v, size_t min_capacity) {
//   if (v->capacity <= min_capacity)
//     return;
// 
//   const size_t new_capacity = min_capacity >= v->length ? min_capacity : v->length;
// 
//   v->data = realloc(v->data, v->esize * new_capacity);
//   v->capacity = new_capacity;
// }

/* modifying elements */
void vector_push(vector *v, const void *src) {
  if (v->length == v->capacity)
    vector_reserve(v, 2 * v->capacity);

  void *dst = (void*)((char*)v->data + v->esize * v->length);
  memcpy(dst, src, v->esize);
  v->length++;
}

// void vector_pop(vector *v, void *dst) {
//   assert(v->length > 0);
// 
//   void *src = (void*)((char*)v->data + v->esize * (v->length - 1));
//   memcpy(dst, src, v->esize);
//   v->length--;
// }

void vector_get(const vector *v, size_t index, void *dst) {
  assert(index < v->length);

  void *src = (void*)((char*)v->data + v->esize * index);
  memcpy(dst, src, v->esize);
}

void vector_set(const vector *v, size_t index, const void *src) {
  assert(index < v->length);

  void *dst = (void*)((char *)v->data + v->esize * index);
  memcpy(dst, src, v->esize);
}

void vector_remove(vector *v, size_t index) {
  assert(index < v->length);

  for (size_t i = index + 1; i < v->length; i++) {
    void *dst = (void*)((char *)v->data + v->esize * (i - 1));
    void *src = (void*)((char *)v->data + v->esize * i);
    memcpy(dst, src, v->esize);
  }

  v->length--;
}

/* direct access */
// void *vector_data(const vector *v) {
//   return v->data;
// }

// void *vector_get_ptr(const vector *v, size_t index) {
//   return (void*)((char*)v->data + v->esize * index);
// }

// slice vector_get_slice(const vector *v, size_t index, size_t length) {
//   assert(index + length <= v->length);
// 
//   return (slice) {
//     .data = (void*)((char*)v->data + v->esize * index),
//     .esize = v->esize,
//     .length = length
//   };
// }
