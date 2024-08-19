#include "vector.h"

void vector_init(vector *v, size_t item_size) {
  v->capacity = VECTOR_INIT_CAPACITY;
  v->total = 0;
  v->items = malloc(item_size * v->capacity);  // void* 배열을 가르키는 items
  v->item_size = item_size;
}

size_t vector_total(vector *v) { return v->total; }

static void vector_resize(vector *v, size_t capacity) {
  if (capacity <= v->total) return;
  void *items = realloc(v->items, v->item_size * capacity);
  if (items) {
    v->items = items;
    v->capacity = capacity;
  }
}

void vector_add(vector *v, void *item) {
  if (v->capacity == v->total) vector_resize(v, v->capacity * 2);
  void *ptr = (char *)v->items + v->total * v->item_size;
  memcpy(ptr, item, v->item_size);
  v->total++;
}

void vector_set(vector *v, size_t index, void *item) {
  // assert(index < v->total);

  void *ptr = (char *)v->items + index * v->item_size;
  memcpy(ptr, item, v->item_size);
}

void vector_get(vector *v, size_t index, void *dst) {
  // assert(index < v->total);  // assert : if not, make program stop

  void *ptr = (char *)v->items + index * v->item_size;
  memcpy(dst, ptr, v->item_size);
}

void vector_delete(vector *v, size_t index) {
  // assert(index < v->total);

  for (size_t i = index; i < v->total - 1; i++) {
    void *pre_ptr = (char *)v->items + i * v->item_size;
    void *sub_ptr = (char *)v->items + (i + 1) * v->item_size;
    memcpy(pre_ptr, sub_ptr, v->item_size);
  }

  v->total--;
}

void vector_free(vector *v) {
  if (v->items == NULL) return;
  free(v->items);
  v->items = NULL;
}