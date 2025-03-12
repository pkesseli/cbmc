#include <stdbool.h>
#include <string.h>
#include <stdlib.h>

#define __CPROVER

#ifndef __CPROVER
void __CPROVER_assume(bool condition);
void __CPROVER_assert(bool condition, const char *message);
#else
#define abs(value) ((value) < 0 ? -(value) : value)
#endif

#define __CPROVER_unique_domain(field, field_domain_array)                                  {                                                                                               size_t index;                                                                               __CPROVER_assume(index < (sizeof(field_domain_array) / sizeof(field_domain_array[0])));     __CPROVER_assume(!field_domain_array##_used[index]);                                        field_domain_array##_used[index] = true;                                                    field = field_domain_array[index];                                                      }

size_t __CPROVER_nondet_array_index(size_t length) {
    size_t index;
    __CPROVER_assume(index < length);
    return index;
}

#define __CPROVER_nondet_index(array)                                  __CPROVER_nondet_array_index(sizeof(array) / sizeof(array[0]))

#define __CPROVER_nondet_element(array)        (array)[__CPROVER_nondet_index(array)]

static size_t __CPROVER_index_tmp;

static size_t __CPROVER_index_dispatch(bool comparison) {
    __CPROVER_assume(comparison);
    return __CPROVER_index_tmp;
}

#define __CPROVER_index(array, value)     __CPROVER_index_dispatch(array[__CPROVER_index_tmp = __CPROVER_nondet_index(array)] == value)

struct House {
    int house_number;
    const char * name;
    const char * nationality;
    const char * book_genre;
    const char * food;
    const char * color;
    const char * animal;
};

static int House_house_number[] = {1, 2, 3, 4, 5};
static bool House_house_number_used[5];
static const char * House_name[] = {"Peter", "Alice", "Bob", "Eric", "Arnold"};
static bool House_name_used[5];
static const char * House_nationality[] = {"norwegian", "german", "dane", "brit", "swede"};
static bool House_nationality_used[5];
static const char * House_book_genre[] = {"fantasy", "biography", "romance", "mystery", "science fiction"};
static bool House_book_genre_used[5];
static const char * House_food[] = {"stir fry", "grilled cheese", "pizza", "spaghetti", "stew"};
static bool House_food_used[5];
static const char * House_color[] = {"red", "green", "blue", "yellow", "white"};
static bool House_color_used[5];
static const char * House_animal[] = {"bird", "dog", "cat", "horse", "fish"};
static bool House_animal_used[5];

static void init_House(struct House * instance) {
    __CPROVER_unique_domain(instance->house_number, House_house_number);
    __CPROVER_unique_domain(instance->name, House_name);
    __CPROVER_unique_domain(instance->nationality, House_nationality);
    __CPROVER_unique_domain(instance->book_genre, House_book_genre);
    __CPROVER_unique_domain(instance->food, House_food);
    __CPROVER_unique_domain(instance->color, House_color);
    __CPROVER_unique_domain(instance->animal, House_animal);
}

struct Solution {
    struct House houses[5];
};

static void init_Solution(struct Solution * instance) {
    for (size_t i = 0; i < sizeof(instance->houses) / sizeof(instance->houses[0]); ++i) {
        init_House(&instance->houses[i]);
    }
}

static void validate(struct Solution solution) {
    typeof(__CPROVER_nondet_element(solution.houses)) norwegian = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(norwegian.nationality == "norwegian");
    __CPROVER_assume(norwegian.book_genre == "fantasy");
    typeof(__CPROVER_nondet_element(solution.houses)) cat_lover = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(cat_lover.animal == "cat");
    typeof(__CPROVER_nondet_element(solution.houses)) biography_reader = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(biography_reader.book_genre == "biography");
    __CPROVER_assume(abs(cat_lover.house_number - biography_reader.house_number) == 1);
    typeof(__CPROVER_nondet_element(solution.houses)) german = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(german.nationality == "german");
    __CPROVER_assume(german.name == "Bob");
    typeof(__CPROVER_nondet_element(solution.houses)) yellow_lover = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(yellow_lover.color == "yellow");
    __CPROVER_assume(yellow_lover.name == "Bob");
    typeof(__CPROVER_nondet_element(solution.houses)) green_lover = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(green_lover.color == "green");
    __CPROVER_assume(green_lover.name == "Peter");
    typeof(__CPROVER_nondet_element(solution.houses)) dane = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(dane.nationality == "dane");
    typeof(__CPROVER_nondet_element(solution.houses)) pizza_lover = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(pizza_lover.food == "pizza");
    __CPROVER_assume(abs(dane.house_number - pizza_lover.house_number) == 2);
    typeof(__CPROVER_nondet_element(solution.houses)) blue_lover = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(blue_lover.color == "blue");
    __CPROVER_assume(blue_lover.house_number < dane.house_number);
    typeof(__CPROVER_nondet_element(solution.houses)) grilled_cheese_lover = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(grilled_cheese_lover.food == "grilled cheese");
    __CPROVER_assume(grilled_cheese_lover.house_number < norwegian.house_number);
    typeof(__CPROVER_nondet_element(solution.houses)) spaghetti_eater = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(spaghetti_eater.food == "spaghetti");
    __CPROVER_assume(spaghetti_eater.name == "Peter");
    typeof(__CPROVER_nondet_element(solution.houses)) horse_keeper = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(horse_keeper.animal == "horse");
    __CPROVER_assume(horse_keeper.name == "Alice");
    typeof(__CPROVER_nondet_element(solution.houses)) fish_enthusiast = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(fish_enthusiast.animal == "fish");
    typeof(__CPROVER_nondet_element(solution.houses)) science_fiction_reader = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(science_fiction_reader.book_genre == "science fiction");
    __CPROVER_assume(fish_enthusiast.house_number + 1 == science_fiction_reader.house_number);
    typeof(__CPROVER_nondet_element(solution.houses)) arnold = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(arnold.name == "Arnold");
    __CPROVER_assume(abs(norwegian.house_number - arnold.house_number) == 2);
    typeof(__CPROVER_nondet_element(solution.houses)) romance_reader = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(romance_reader.book_genre == "romance");
    typeof(__CPROVER_nondet_element(solution.houses)) brit = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(brit.nationality == "brit");
    __CPROVER_assume(romance_reader.house_number == brit.house_number);
    __CPROVER_assume(abs(norwegian.house_number - horse_keeper.house_number) == 3);
    typeof(__CPROVER_nondet_element(solution.houses)) bird_keeper = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(bird_keeper.animal == "bird");
    typeof(__CPROVER_nondet_element(solution.houses)) red_lover = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(red_lover.color == "red");
    __CPROVER_assume(bird_keeper.house_number == red_lover.house_number);
    typeof(__CPROVER_nondet_element(solution.houses)) dog_owner = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(dog_owner.animal == "dog");
    __CPROVER_assume(dog_owner.house_number + 1 == fish_enthusiast.house_number);
    typeof(__CPROVER_nondet_element(solution.houses)) stew_lover = __CPROVER_nondet_element(solution.houses);
    __CPROVER_assume(stew_lover.food == "stew");
    __CPROVER_assume(stew_lover.house_number == norwegian.house_number);
}

#ifndef __CPROVER
void __CPROVER_output(const char *name, struct Solution solution);
#endif

int main(void) {
    struct Solution solution;
    init_Solution(&solution);
    validate(solution);

    __CPROVER_output("solution", solution);
    __CPROVER_assert(false, "");
}
