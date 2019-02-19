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

/* Comment in "#define DEBUG" to enable mm_check to check heap consitensy 
 * Usage: add theses lines into the code where mm_check is suposed to be called
 *  
   #ifdef
   #define CHECKHEAP(verbose) printf("%s\n", __func__); mm_check(verbose);
   #endif
 */

#define DEBUG 


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
 * mm_check - Checks the integrety and consitancy of the heap
 */ 
int mm_check(void) 
{
    /*    ToDo:
     * Is every block in the free list marked as free?
     * Are there any contiguous free blocks that somehow escaped coalescing?
     * Is every free block actually in the free list?
     * Do the pointers in the free list point to valid free blocks?
     * Do any allocated blocks overlap?
     * Do the pointers in a heap block point to valid heap addresses?
     * 
     * It returns a nonzero value if and only if the heap is consistent
     */ 

    return 0;
}