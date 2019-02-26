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
 * mm.c - Simple allocator based on an explisit freelist. Stay tuned for more info!
 *
 * Each block has header and footer of the form:
 * 
 *      31  30 29 28  ...  5  4  3  2  1  0 
 *      -------------------------------------
 *     | s  s  s  s   ...  s  s  s  0  0  a/f
 *      ------------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 * 
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
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
    "Hallgrímur Snær Andrésson",
    /* Third member's email address (leave blank if none) */
    "hallgrimura17@ru.is"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* 
void *mem_sbrk(int incr);   Increases the breakpointer
void *mem_heap_lo(void);    Return pointer to first byte in heap
void *mem_heap_hi(void);    Return pointer to last byte in heap
size_t mem_heapsize(void);  Return the current size of the heap in bytes
size_t mem_pagesize(void);  Returns the system’s page size in bytes (4K on Linux systems).
*/
/* ---------------------------------------------------- */
/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<6)  /* initial heap size (bytes) */
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

#define NEXT_FREE_BLKP(bp) ((char*)*(size_t*)((bp) + WSIZE))
#define PREV_FREE_BLKP(bp) ((char*)*(size_t*)(bp))
/* $end mallocmacros */

/* Comment in "#define DEBUG" to enable mm_check to check heap consitensy 
 * Usage: add theses lines into the code where mm_check is suposed to be called
 *  
    #ifdef DEBUG
    printf("%s\n", __func__); mm_check(1);
    #endif
 */

#define DEBUG

/* Global variables */
static char *heap_prologue;  /* pointer to the start of heap */
static char *heap_epilogue;  /* pointer to the end of heap */
static char *free_listp;     /* pointer to the start of free_list */

/* function prototypes for internal helper routines */
int mm_check(int verbose);
int checkFreeBlockIsInFreeList(char *bp);
int checkValidBlock(char *bp);
int checkBlockOverlap(char *bp);
int checkIfTwoContinuousFreeBlocks(char *bp);
int checkIfOutOfBounds(char *bp);
static void printblock(void *bp); 

static int LIFO_insert(char* bp);
static int LIFO_remove(char* bp);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // IMPORTANT: reset all variables including global variables
    /* init empty heap */
    if ((heap_prologue = mem_sbrk(WSIZE << 2)) == NULL) { return -1; }
    PUT(heap_prologue, 0);                          /* Alignment padding */
    PUT((heap_prologue+WSIZE), PACK(OVERHEAD, 1));  /* prolouge header */
    PUT(heap_prologue+DSIZE, PACK(OVERHEAD, 1));    /* prolouge footer */
    PUT(heap_prologue+WSIZE+DSIZE, PACK(0, 1));     /* epilouge header */
    heap_prologue += DSIZE;
    heap_epilogue = NULL;
    free_listp = NEXT_BLKP(heap_prologue);
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE>>2) == NULL) {return -1; }

    #ifdef DEBUG
    printf("%s\n", __func__); mm_check(1);
    #endif
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 * Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int new_size = ALIGN(size) + SIZE_T_SIZE;    /* make the size a multiple of 8 */
    char* bp = free_listp;
    while(bp != 0) {
        if(!(GET_SIZE(HDRP(bp)) <= new_size)) {
            printf("size break\n");
            break;
        }
        printf("size break\n");
        bp = NEXT_FREE_BLKP(bp);
    }
    if(new_size < GET_SIZE(HDRP(bp)) - 3*WSIZE ) {       //now we split
       size_t free_size = GET_SIZE(HDRP(bp)) - new_size;   /* remaining free block size */
        printf("size %d newsize %d hdrpbp %p\n", free_size, new_size,HDRP(bp)); 
        PUT(FTRP(bp), PACK(free_size, 0));          /* update free footer size */
        PUT(HDRP(bp), PACK(new_size, 1));           /* new allocated header */  
        PUT(FTRP(bp), PACK(new_size, 1));           /* new allocated footer */
        PUT(HDRP(NEXT_BLKP(bp)), PACK(free_size, 0));     /* new free header */
        LIFO_insert(bp);
    }
    else {
        PUT(FTRP(bp), PACK(GET_SIZE(FTRP(bp)), 1));      /* update free footer size */
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));      /* new free header */
        LIFO_remove(bp);
    }
    
    
    #ifdef DEBUG
    printf("%s\n", __func__); mm_check(1);
    #endif

    return (void*)bp;
}

/*
 * mm_free - Freeing a block does nothing.
 * ToDo: we want to mark the area as free and update surrounding headers if necessary
 */
void mm_free(void *bp)
{
    /* If bp is nullptr or heap uninitilized */
    if(bp == 0 || heap_prologue == 0) { return; }
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));    /* mark header as free */
    PUT(FTRP(bp), PACK(size, 0));    /* maek footer as free */

    coalesce(bp);
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

/****************************** Helper Functions ********************************/
/********************************************************************************/

static int LIFO_insert(char* bp) {
    printf("bp %p\n", bp);
    if(bp == 0) {
        free_listp = bp;
        printf("get out\n");
        return 0;
    }

    if(bp != free_listp) {
        PUT(PREV_FREE_BLKP(bp) + WSIZE, (size_t)NEXT_FREE_BLKP(bp));    /* Prev's next = next */ 
    }
    if(NEXT_FREE_BLKP(bp) != 0) {
        PUT(NEXT_FREE_BLKP(bp), (size_t)PREV_FREE_BLKP(bp));            /* Next's prev = prev */
        char* fp = NEXT_BLKP(bp);                       /* Pointer to new free-block */
        PUT(fp, (size_t)NULL);                          /* fb's prev = NULL */
        PUT((fp + WSIZE), (size_t)free_listp);          /* fb's next = the start of the free list */   
        free_listp = fp;                                /* the freelist starts with fb */
    }
    #ifdef DEBUG
    printf("%s\n", __func__); mm_check(1);
    #endif

    return 1;
}
static int LIFO_remove(char* bp) {
    if(bp == 0) {
        return 0;
    }
    if(bp != free_listp) {
        PUT(PREV_FREE_BLKP(bp) + WSIZE, (size_t)NEXT_FREE_BLKP(bp));    /* Prev's next = next */ 
    }
    if(NEXT_FREE_BLKP(bp) != 0) {
        PUT(NEXT_FREE_BLKP(bp), (size_t)PREV_FREE_BLKP(bp));            /* Next's prev = prev */
    }
    return 1;
}


/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    /* Allocate an even number of words to maintain alignment */
    size_t size = ((words+1) & -0x2) << 0x2;
    // size_t size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    // size = (words & -2) ? words << 2 : (words+1) << 2;
    if ((bp = mem_sbrk(size)) == (void *)-1) { return NULL; }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));           /* free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* new epilogue header */
    heap_epilogue = NEXT_BLKP(bp);          /* update heap_epilogue pointer */
    PUT(bp + WSIZE, 0); /* make free block's next pointer point to null */
    LIFO_insert(bp);    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1: Both blocks are allocated, no coalessing reqired */
        return bp;
    }
    else if (prev_alloc && !next_alloc) {      /* Case 2: Next block is free */
        // ToDo: remove next block from free list
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
        // ToDo: add coalesed block free list
    }
    else if (!prev_alloc && next_alloc) {      /* Case 3: Previous block is free */
        // ToDo: remove prev block from free list
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // ToDo: add coalesed block free list
    }
    else {                                     /* Case 4: Both blocks are free  */
        // ToDo: remove next block from free list
        // ToDo: remove prev block from free list
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        // ToDo: add coalesed block free list
    }

    #ifdef DEBUG
    printf("%s\n", __func__); mm_check(1);
    #endif

    return bp;
}

/****************************** Checker Functions *******************************/
/********************************************************************************/

/*
 * mm_check - Checks the integrety and consitancy of the heap.
 * 
 * The checker is written for our pending implenentation so we are ....
 * 
 * Returns a nonzero value if and only if the heap is consistent.
 */ 
int mm_check(int verbose) 
{
    /*    ToDo:
     * Is every block in the free list marked as free?                          - Done
     * Are there any contiguous free blocks that somehow escaped coalescing?    - Done
     * Is every free block actually in the free list?                           - Done
     * Do the pointers in the free list point to valid free blocks?             - Done
     * Do any allocated blocks overlap?                                         - Semi
     * Do the pointers in a heap block point to valid heap addresses?           - Done
     */ 

    // char *bp = heap_prologue;    /* pointer to the beginning of the heap */
    // char *f_list = free_listp;  /* pointer to the end of the heap */
    /* Run through the heap implicitly */
    for (char *bp = heap_prologue; 0 < GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)) { /* check all blocks on heap */
        if(verbose) { printblock(bp); }
        if(!checkFreeBlockIsInFreeList(bp))     { return 0; }      
        if(!checkValidBlock(bp))                { return 0; }
        if(!checkBlockOverlap(bp))              { return 0; }
        if(!checkIfTwoContinuousFreeBlocks(bp)) { return 0; }
        if(!checkIfOutOfBounds(bp))             { return 0; }
    }

    /* Run through the free list */
    for (char *f_list = free_listp; f_list != 0; f_list = NEXT_FREE_BLKP(f_list)) { /* The second word in the "payload" is the pointer to the next free block */
        
        if((int)f_list & 0x7) {             /* The pointer is not 8bit alinged */
            printf("Error: the free block %p is not 8bit allinged\n", (void*)f_list);
           return 0;
        }

        if(heap_epilogue < f_list || f_list < heap_prologue) { /* The pointers in the free block point out of bounds */
            printf("Error: the free block %p points out of bounds    %p < %p || %p < %p\n", (void*)f_list, (void*)heap_epilogue, (void*)f_list,  (void*)f_list, (void*)heap_prologue);
            return 0;
        }

        if(GET_ALLOC(HDRP(f_list))) {   /* The block is alocated */
            printf("Error: the free block %p is not free (alocated)\n", (void*)f_list);
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
    if(GET_ALLOC(HDRP(bp)) == 0) {      /* if block is free */
        for(char *f_list = free_listp; f_list != bp; f_list = NEXT_FREE_BLKP(f_list)) {
            if (f_list == NULL) {    /* reached end of free list */
                printf("Error: the free block %p is not in the free list\n", bp);
                return 0;
            }
        }
    }
    return 1; /* block is in the freelist */
}

/*
 * - checkValidHeap -
 */
int checkValidBlock(char *bp) 
{
    if((size_t)bp & 0x7) {
        printf("Error: %p is not 8bit aligned\n", bp);
        return 0;
    }
    if(GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: in block %p header does not match footer  h%p f%p\n" , (void*)bp, (void*)GET(HDRP(bp)), (void*)GET(FTRP(bp)));
        return 0;
    }
    return 1; /* block passed */
}

int checkBlockOverlap(char *bp) 
{
    if (FTRP(bp) > HDRP(NEXT_BLKP(bp))) {
        printf("Error: blocks %p and %p overlap\n", bp, NEXT_BLKP(bp));
        return 0;
    }
    return 1;
}

int checkIfTwoContinuousFreeBlocks(char *bp) 
{
    if(GET_ALLOC(HDRP(bp)) == 0) { // 2 adjecent free blocks ?
        if(GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0) {
            printf("Error: block %p and %p are free adjecent blocks", PREV_BLKP(bp), bp);
            return 0;
        }
    }
    return 1;
}

int checkIfOutOfBounds(char *bp) 
{
    if(heap_epilogue < NEXT_BLKP(bp) || PREV_BLKP(bp) < heap_prologue) { /* The pointers in the free block point out of bounds */
        printf("Error: the block %p is out of bounds\n", (void*)bp);
        return 0;
    }
    return 1;
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: h: [%d:%c] f: [%d:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}