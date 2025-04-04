#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <math.h>

typedef enum {
    PINDEX_FOUND = 0x0,
    PINDEX_PRIME = 0x1,
    PINDEX_NOT_PRIME = 0x2,
} PrimeTableIndexEnum;

struct PrimeTableIndex {
    PrimeTableIndexEnum status;
    uint64_t index;
};

typedef struct PrimeTableIndex PrimeTableIndex;

struct PrimePrecompute {
    uint64_t max_prime;
    uint8_t *prime_table;
    uint64_t *psearch_reminders;
    uint64_t *num_primes;
    uint64_t *num_primes3;
    uint64_t prime_list_size;
    uint64_t *prime_list;
};

typedef struct PrimePrecompute PrimePrecompute;

void find_prime_table_index(uint64_t num, PrimePrecompute* precompute, PrimeTableIndex* index) {
    // 2 is the only even prime so we treat it differently
    if(num < 24llu && (num==3 || num==5 || num==7 || num==11 || num==13 || num==17 || num==19 || num==23)) {
        index->status = PINDEX_PRIME;
        index->index = 0;
        return;
    }
    if(!(num%2 && num%3 && num%5 && num%7 && num%11 && num%13 && num%17 && num%19 && num%23)) {
        index->status = PINDEX_NOT_PRIME;
        index->index = 0;
        return;
    }
    index->status = PINDEX_FOUND;
    uint64_t rem = num % 223092870llu;    //product P of all primes up to 23;  llu - unsigned long long
    uint64_t* rem_table = precompute->psearch_reminders;
    size_t max_index = 36495360llu;   // number of remainders mod P coprime with P
    size_t min_index = 0;   //zero
    size_t mid_index;     //used for binary search purposes
    while(max_index - min_index > 8llu) {
        mid_index = min_index + (max_index - min_index) / 2llu;
        if(rem_table[mid_index] > rem) {
            max_index = mid_index;
        } else {
            min_index = mid_index;
        }
    }
    while(rem_table[min_index] != rem) {
        assert(min_index <= max_index && "Missing coprime");     //signal to show that the code does not work properly
        min_index++;
    }
    index->index = 36495360llu * (num / 223092870llu) + min_index;
    return;
}

uint64_t prime_from_index(size_t index, PrimePrecompute* precompute) {
    return 223092870llu * (index / 36495360llu) + precompute->psearch_reminders[index % 36495360llu];   //indexing coprimes with P
}

void load_reminders(PrimePrecompute *prime_precompute) {             //compute remainders mod P which are coprime with P
    uint64_t *psearch_reminders = malloc(36495360llu * sizeof(uint64_t));
    prime_precompute->psearch_reminders = psearch_reminders;
    size_t index = 0;
    for (size_t i = 0; i < 223092870llu; i++) {
        if (i%2 && i%3 && i%5 && i%7 && i%11 && i%13 && i%17 && i%19 && i%23) {
            psearch_reminders[index] = i;
            index += 1;
            assert(index <= 36495360 && "bug - too many coprimes????");   //should not appear if the code works properly
        }
    }
    assert(index == 36495360 && "bug - not exact coprimes????");  //should not appear if code works properly
}

void build_prime_table(PrimePrecompute *prime_precompute) {
    uint64_t *psearch_reminders = prime_precompute->psearch_reminders;
    uint64_t num_blocks = (prime_precompute->max_prime + 223092870llu - 1llu) / 223092870llu;
    uint64_t num_bits = num_blocks * 36495360llu + 1llu;
    size_t num_bytes = (num_bits + 7llu) / 8llu;
    uint8_t *table = malloc(num_bytes);
    if(table == NULL)
        return;

    memset(table, -1, num_bytes);

    prime_precompute->prime_table = table;
    // 1 is not prime, this marks it
    table[0] = 0b11111110;
    uint64_t primes = 0;
    uint64_t primes3 = 0;
    for(uint64_t i = 0; i < num_bits; i++) {
        if(!(table[i >> 3] & (1 << (i & 7)))) {
            continue;
        }
        uint64_t num = prime_from_index(i, prime_precompute);
        if (num > prime_precompute->max_prime)
            break;

        primes++;
        if(num % 4 == 3)
            primes3++;

        for(uint64_t num_multiple = 2llu * num; num_multiple < prime_precompute->max_prime; num_multiple+=num) {
            PrimeTableIndex table_index;
            find_prime_table_index(num_multiple, prime_precompute, &table_index);
            if(table_index.status != PINDEX_FOUND) {
                continue;
            }
            uint64_t index = table_index.index;
            table[index >> 3] = table[index >> 3] & ~(1 << (index & 7));
        }
    }
    return;
}

void build_prime_counts(PrimePrecompute *prime_precompute) {             //count number of primes up to x
    uint64_t num_blocks = prime_precompute->max_prime / 8192llu + 1;
    uint64_t *num_primes = malloc(num_blocks * sizeof(uint64_t));
    if(num_primes == NULL) {
        return;
    }

    uint64_t *num_primes3 = malloc(num_blocks * sizeof(uint64_t));
    if(num_primes == NULL) {
        free(num_primes);
        return;
    }

    prime_precompute->num_primes = num_primes;
    prime_precompute->num_primes3 = num_primes3;
    size_t index = 0;
    uint64_t pc = 0;
    uint64_t p3c = 0;

    for(uint64_t i = 0; 1; i++) {
        uint64_t prime_num = prime_from_index(i, prime_precompute);
        if(prime_num > prime_precompute->max_prime)
            break;

        if(prime_precompute->prime_table[i >> 3] & (1 << (i & 7))) {
            while(index < prime_num / 8192llu + 1) {
                num_primes[index] = pc;
                num_primes3[index] = p3c;
                index++;
            }
            pc++;
            if(prime_num % 4 == 3) {
                p3c++;
            }
        }
    }

    while(index < num_blocks) {
        num_primes[index] = pc;
        num_primes3[index] = p3c;
        index++;
    }

    for(uint64_t i = 1; i < num_blocks; i++) {
        num_primes[i] += 8;
        num_primes3[i] += 5;
    }
}

struct PrimeCounts {
    uint64_t prime_count;
    uint64_t prime3_count;
};

typedef struct PrimeCounts PrimeCounts;

void count_primes(uint64_t num, PrimeCounts *prime_counts, PrimePrecompute *prime_precompute) {
    assert(num <= prime_precompute->max_prime && "Precompute is too small");
    uint64_t index = num / 8192llu;
    uint64_t pc = prime_precompute->num_primes[index];
    uint64_t p3c = prime_precompute->num_primes3[index];
    uint64_t i = index * 8192llu;
    PrimeTableIndex pt_index;
    while(i<=num) {
        find_prime_table_index(i, prime_precompute, &pt_index);
        if(pt_index.status == PINDEX_PRIME || \
        pt_index.status == PINDEX_FOUND && (prime_precompute->prime_table[pt_index.index >> 3] & (1 << (pt_index.index & 7)))) {
            pc++;
            if(i % 4 == 3)
                p3c++;
        }
        i++;
    }
    prime_counts->prime_count = pc;
    prime_counts->prime3_count = p3c;
}

void build_prime_list(PrimePrecompute *prime_precompute) {
    uint64_t list_size = prime_precompute->prime_list_size;
    uint64_t *list = malloc(list_size * sizeof(uint64_t));
    if (list == NULL)
        return;

    prime_precompute->prime_list = list;
    size_t index = 0;
    for(uint64_t i = 0; i < 24 && index < list_size; i++) {
        if(i==3 || i==5 || i==7 || i==11 || i==13 || i==17 || i==19 || i==23) {
            list[index] = i;
            index++;
        }
    }

    for(uint64_t i = 0; index < list_size; i++) {
        if(prime_precompute->prime_table[i >> 3] & (1 << (i & 7))) {
            list[index] = prime_from_index(i, prime_precompute);
            index++;
        }
    }
}

static uint64_t upperbound_prime(uint64_t x) {  //calculate Dusart upper bound x/(log x) * [1 + 1/log x + 2/log^2 x + 7.59/log^3 x], valid for all x > 1
    double log_x = nextafter(log(nextafter(x, -INFINITY)), -INFINITY);   //rounding from below, since we divide by log
    double log_x_pow2 = nextafter(log_x * log_x, -INFINITY);
    double part = nextafter(nextafter(7.59, INFINITY) / nextafter(log_x * log_x_pow2, -INFINITY), INFINITY);  //upper bound for 7.59/log^3 x term in parts
    part = nextafter(part + nextafter(2. / log_x_pow2, INFINITY), INFINITY);
    part = nextafter(part + nextafter(1. / log_x, INFINITY), INFINITY);
    part = nextafter(part + 1., INFINITY);
    double x_float = nextafter(x, INFINITY);
    double estimate = nextafter(nextafter(x_float / log_x, INFINITY) * part, INFINITY);
    return ((uint64_t)estimate) + 1;
}

static uint64_t lowerbound_prime3(uint64_t x) {   //calculate lower bound for primes 3 mod 4 from Corollary 2.5 in the paper
    double log_x = nextafter(log(nextafter(x, INFINITY)), INFINITY);
    double pcf = nextafter(1. / nextafter(2. * log_x, INFINITY), -INFINITY);
    double pcf_part2 = nextafter(nextafter(.473, -INFINITY) / nextafter(log_x * log_x, INFINITY), -INFINITY);
    pcf = nextafter(pcf + pcf_part2, -INFINITY);
    double x_float = nextafter(x, -INFINITY);
    double estimate = nextafter(x_float * pcf, -INFINITY);
    return ((uint64_t)estimate) - 1;
}

int main() {
    //uint8_t *psearch_reminders = NULL;
    //uint8_t *prime_table = NULL;
    PrimePrecompute prime_precompute = {
        .max_prime = 1000000000llu,    //has to be above 10^7 to work;  for 10^11 - ~ 1 hour
        .prime_table = NULL,
        .psearch_reminders = NULL,
        .num_primes = NULL,
        .num_primes3 = NULL,
        .prime_list_size = 0,
        .prime_list = NULL
    };
    printf("Precompute remainders \n");
    fflush(stdout);
    load_reminders(&prime_precompute);
    printf("Precompute prime table \n");
    fflush(stdout);
    build_prime_table(&prime_precompute);
    printf("Precompute prime counts \n");
    fflush(stdout);
    build_prime_counts(&prime_precompute);
    printf("Precompute prime list \n");
    fflush(stdout);
    PrimeCounts prime_counts;
    count_primes(10000000llu, &prime_counts, &prime_precompute);
    prime_precompute.prime_list_size = prime_counts.prime_count;
    build_prime_list(&prime_precompute);

    printf("Starting compute \n");
    fflush(stdout);

    uint64_t numerator, denominator;
    size_t index = 0;
    size_t p3_index = 0;
    for(uint64_t i = 9; i < 12000000000000llu; i+=2 * (4 * numerator - denominator)) {   //multiply by 2, as even numbers are not prime
        p3_index = index = numerator = denominator = 0;
        while(1) {
            uint64_t prime_num = prime_precompute.prime_list[index];
            if(prime_num * prime_num > i) {
                break;
            }
            uint64_t limit = i / prime_num;
            if (limit > prime_precompute.max_prime) {
                prime_counts.prime_count = upperbound_prime(limit);
                prime_counts.prime3_count = lowerbound_prime3(limit);
            } else {
                count_primes(limit, &prime_counts, &prime_precompute);
            }
            denominator += prime_counts.prime_count;
            denominator -= index;
            if(prime_num % 4 == 3) {
                numerator += prime_counts.prime3_count - p3_index;
                p3_index++;
            }
            index++;
        }
        if(i / 3 > prime_precompute.max_prime)
            printf("(using estimates) ");
        printf("x: %llu numerator: %llu denominator: %llu step: %llu\n", i, numerator, denominator, 4 * numerator - denominator);
        printf("ratio: ~ %.5lf\n\n", (double)numerator / denominator);
        fflush(stdout);
        if(4 * numerator < denominator)
            break;
    }

    return 0;
}
