/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * -------------------------------------------------------------------
 * mm.c - Simple allocator based on
 *
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in below _AND_ in the
 * struct that follows.
 *
 * Note: This comment is parsed. Please do not change the
 *       Format!
 *
 * === User information ===
 * Group: Pending-group-name
 * User 1: egilltor17
 * SSN: 250697-2529
 * User 2: ernir17
 * SSN: 180996-4279
 * User 3: hallgrimura17
 * SSN: 040396-2929
 * === End User Information ===
 ********************************************************/
team_t team = {
    /* Group name */
    "Pending-group-name",
    /* First member's full name */
    "Egill Torfason",
    /* First member's email address */
    "egilltor17@ru.is",
    /* Second member's full name (leave blank if none) */
    "Ernir Snær Helgason",
    /* Second member's email address (leave blank if none) */
    "ernir17@ru.is",
    /* Third full name (leave blank if none) */
    "Hallgræimur Snær Andrésson",
    /* Third member's email address (leave blank if none) */
    "hallgrimura17@ru.is"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* ---------------------------------------------------- */
/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)         (*(size_t *)(p))
#define PUT(p, val)    (*(size_t *)(p) = (val))

/* (which is about 49/100).* Read the size and allocated fields from address p */
#define GET_SIZE(p)    (GET(p) & ~0x7)
#define GET_ALLOC(p)   (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* Comment in "#define DEBUG" to enable mm_check to check heap consitensy 
 * Usage: add theses lines into the code where mm_check is suposed to be called
 *  
   #ifdef
   #define CHECKHEAP(verbose) printf("%s\n", __func__); mm_check(verbose);
   #endif
 */

#define DEBUG 

/* Global variables */
static char *heap_prologe;  /* pointer to the start of heap */
static char *heap_epiloge;  /* pointer to the end of heap */
static char *free_listp;    /* pointer to the start of free_list */

/* function prototypes for internal helper routines */
int mm_check(void);
int checkFreeBlockIsInFreeList(char *bp);
int checkValidBlock(char *bp);
int checkBlockOverlap(char *bp);
int checkIfTwoContinuousFreeBlocks(bp);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // IMPORTANT: reset all variables including global variables
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1) {
        return NULL;
    }
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 * ToDo: we want to mark the area as free and update surrounding headers if necessary
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize) {
        copySize = size;
    }
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * mm_check - Checks the integrety and consitancy of the heap.
 * Returns a nonzero value if and only if the heap is consistent.
 */ 
int mm_check(vrebose) 
{
    /*    ToDo:
     * Is every block in the free list marked as free?                          - Done
     * Are there any contiguous free blocks that somehow escaped coalescing?    - Done
     * Is every free block actually in the free list?                           - Done
     * Do the pointers in the free list point to valid free blocks?             - Done
     * Do any allocated blocks overlap?                                         - 
     * Do the pointers in a heap block point to valid heap addresses?           - 
     */ 

    char *bp = heap_prologe;    /* pointer to the beginning of the heap */
    char *f_list = free_listp;  /* pointer to the end of the heap */
    int lastAlocated = 1;

    /* Run through the heap implisitly */
    for (bp; 0 < GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)) { /* check all blocks on heap */

        if (!checkFreeBlockIsInFreeList(bp))    { return 0; }      
        if (!checkValidBlock(bp))               { return 0; }
        if (!checkBlockOverlap())               { return 0; }
        if (!checkIfTwoContinuousFreeBlocks(bp)){ return 0; }

    }

    /* Run through the free list */
    while (f_list != head_epiloge) {
        f_list = *(f_list + WSIZE)      /* The second word in the "payload" is the pointer to the next free block */

        if (!(f_list % 8)) {            /* The pointer is not 8bit alinged */
            printf("Error: the free block %p is not 8bit allinged\n", f_list);
            return 0;
        }

        if (GET_ALLOC(HDRP(f_list))) {  /* The block is alocated */
            printf("Error: the free block %p is not free (alocated)\n", f_list);
            return 0;
        }

        
    }  

    return 1;
}

/*
 * - checkFreeBlockIsInFreeList -
 * Returns a non zero number if a free block is in the free list.
 */
int checkFreeBlockIsInFreeList(char *bp)
{
    if (GET_ALLOC(HDRP(bp)) == 0) { /* if free block */
        char *f_list = free_listp;

        while (bp != f_list) {
            f_list = *(f_list + WSIZE) /* WARNING f_next er EKKI til (hvernig traverse free list??) */

            if (f_list == nullptr) { /* reached end of free list */
                printf("Error: the free block %p is not in the free list\n", bp);
                return 0;
            }
        }
    }
    return 1; /* block is in the freelist */
}

/*
 * - checkValidHeap -
 *
 *
 */
int checkValidBlock(char *bp)
{
    if ((size_t)bp % 8) {
        printf("Error: %p is not doubleword aligned\n", bp);
        return 0;
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: in block %p header does not match footer\n", bp);
        return 0;
    }
    return 1; /* every block has been checked */
}


int checkIfTwoContinuousFreeBlocks(char *bp) {
    if (GET_ALLOC(HDRP(bp)) == 0) { // 2 adjecent free blocks ?
            if (GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0) {
                printf("Error: block %p and %p are free adjecent blocks", PREV_BLKP(bp), bp);
                return 0;
            }
        }
}
