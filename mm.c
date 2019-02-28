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

/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define MINBLOCK    16      /* minimum size of a free block (bytes) */
#define ALIGNMENT   8       /* single word (4) or double word (8) alignment */

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

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

/* Given block ptr bp, compute address of next and previous free blocks */
#define NEXT_FREE_BLKP(bp) ((char*)GET((bp) + WSIZE))
#define PREV_FREE_BLKP(bp) ((char*)GET(bp))


/* 
 * Comment in "#define DEBUG" to enable mm_check to check heap consitensy 
 * Usage: add theses lines into the code where mm_check is suposed to be called
 *  
    #ifdef DEBUG
    printf("%s\n", __func__); mm_check(1);
    #endif
 *
 * ===================================================================================== */

// #define DEBUG

/* ===================================================================================== */


/* Global variables */
static char *heap_prologue;  /* pointer to the start of heap */
static char *heap_epilogue;  /* pointer to the end of heap */
static char *free_listp;     /* pointer to the start of free list */
static char *skip_listp;     /* pointer to the start of skip list */

/* function prototypes for internal helper routines */
static void LIFO_insert(char* bp);
static void LIFO_remove(char* bp);
static void *coalesce(void *bp);

int mm_check(int verbose);
static int checkFreeBlockIsInFreeList(char *bp);
static int checkValidBlock(char *bp);
static int checkBlockOverlap(char *bp);
static int checkIfTwoContinuousFreeBlocks(char *bp);
static int checkIfOutOfBounds(char *bp);
static void printblock(void *bp); 


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // IMPORTANT: reset all variables including global variables
    /* init empty heap */
    if ((heap_prologue = mem_sbrk(WSIZE << 2)) == NULL) { return -1; }
    PUT(heap_prologue, 0);                          /* Alignment padding */
    PUT(heap_prologue+WSIZE, PACK(OVERHEAD, 1));    /* prolouge header */
    PUT(heap_prologue+DSIZE, PACK(OVERHEAD, 1));    /* prolouge footer */
    PUT(heap_prologue+WSIZE+DSIZE, PACK(0, 1));     /* epilouge header */
    heap_prologue += DSIZE;
    heap_epilogue = heap_prologue + DSIZE;
    free_listp = 0;

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
    size_t new_size = ALIGN(size) + SIZE_T_SIZE;    /* make the size a multiple of 8 */
    size_t free_size;                               /* remaining free block size */
    char* bp = free_listp;
    
    if (size <= 0) { return NULL; }                 /* Invalid size */

    /* run through the freelist until a sufficiently large block is found else bp = 0 */
    for(bp = free_listp; ((size_t)bp && (new_size > GET_SIZE(HDRP(bp)))); bp = NEXT_FREE_BLKP(bp)) {/* printf("%p\n", bp); */}
    

    if(!bp) {                                           /* if there is no suitable free block we extend */
        size_t size = (((MAX(new_size, CHUNKSIZE)) + 1) & -2);
        if ((bp = mem_sbrk(size)) == (void *)-1) { return NULL; }

        /* Initialize free block header/footer and the epilogue header */
        PUT(HDRP(bp), PACK(size, 0));           /* free block header */
        PUT(FTRP(bp), PACK(size, 0));           /* free block footer */
        PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* new epilogue header */
        heap_epilogue = NEXT_BLKP(bp);          /* update heap_epilogue pointer */
        
        bp = coalesce(bp);                      /* Coalesce if the previous block was free */
    }

    free_size = GET_SIZE(HDRP(bp)) - new_size;          /* remaining free block size */
    if(free_size >= (DSIZE + OVERHEAD)) {               /* the block is big enugh to be split */
        LIFO_remove(bp);
        PUT(FTRP(bp), PACK(free_size, 0));              /* update free footer size */
        PUT(HDRP(bp), PACK(new_size, 1));               /* update free haader with allocated header */  
        PUT(FTRP(bp), PACK(new_size, 1));               /* new allocated footer */
        PUT(HDRP(NEXT_BLKP(bp)), PACK(free_size, 0));   /* new free header */
        LIFO_insert(NEXT_BLKP(bp));
    }
    else {                                              /* we pad */
        LIFO_remove(bp);
        PUT(HDRP(bp), PACK(GET_SIZE(HDRP(bp)), 1));     /* update the header allocation */
        PUT(FTRP(bp), PACK(GET_SIZE(FTRP(bp)), 1));     /* update the footer allocation */
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

    #ifdef DEBUG
    printf("%s\n", __func__); mm_check(1);
    #endif
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void* newptr;
    size_t total_size;
    size_t new_size = ALIGN(size) + SIZE_T_SIZE;    /* make the size a multiple of 8 */
    if(ptr == NULL) {                               /* pointer is invalid, malloc new block*/
        return mm_malloc(size);
    }
    else if(size == 0) {                            /* size is zero, free the pointer */
        mm_free(ptr);
        return NULL;
    }
    else if(new_size <= GET_SIZE(HDRP(ptr))) {      /* the block is big enugh no resize needed */
        return ptr;
    }
    /* the size shrinks */
    else if(new_size <= (GET_SIZE(HDRP(ptr)) - (DSIZE + OVERHEAD))) {
        PUT(FTRP(ptr), PACK(GET_SIZE(HDRP(ptr)), 0));               /* update free footer size */
        PUT(HDRP(ptr), PACK(new_size, 1));                          /* update free header with allocated header */  
        PUT(FTRP(ptr), PACK(new_size, 1));                          /* new allocated footer */
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(GET_SIZE(HDRP(ptr)), 0));    /* new free header */
        LIFO_insert(NEXT_BLKP(ptr));
        coalesce(NEXT_BLKP(ptr));
        return ptr;
    }
    /* there is an adjacent free block, expand the alocation */
    else if((!GET_ALLOC(HDRP(newptr = NEXT_BLKP(ptr)))) && (new_size <= (total_size = GET_SIZE(HDRP(newptr)) + GET_SIZE(HDRP(ptr))))) {
        LIFO_remove(newptr);
        if(total_size - new_size >= (DSIZE + OVERHEAD)) {
            PUT(HDRP(ptr), PACK(new_size, 1));                      /* update free haader with allocated header */  
            PUT(FTRP(ptr), PACK(new_size, 1));                      /* new allocated footer */
            newptr = NEXT_BLKP(ptr);
            PUT(HDRP(newptr), PACK((total_size - new_size), 0));    /* new free header */
            PUT(FTRP(newptr), PACK((total_size - new_size), 0));    /* update free footer size */
            LIFO_insert(newptr);
        }
        else {
            PUT(HDRP(ptr), PACK(total_size, 1));    /* update the header allocation */
            PUT(FTRP(ptr), PACK(total_size, 1));    /* update the footer allocation */
        }
        return ptr;
    }
    else {                                          /* the block needs to be reallocated */
        if ((newptr = mm_malloc(size)) == NULL) {
            printf("ERROR: mm_malloc failed in mm_realloc\n");
            exit(1);
        }
        memcpy(newptr, ptr, ((size < GET_SIZE(HDRP(ptr))) ? size : GET_SIZE(HDRP(ptr))));
        mm_free(ptr);
        return newptr;   
    }
}

/****************************** Helper Functions ********************************/
/********************************************************************************/

static void LIFO_insert(char* bp) {
    if(free_listp == (void*)NULL) {                       /* the list is empty */
        PUT(bp + WSIZE, 0);                     /* bp's next = 0 */
        PUT(bp, 0);                             /* bp's prev = 0 */
        free_listp = bp;                        /* the freelist starts with fb */
    } 
    else {
        PUT(free_listp, (size_t)bp);            /* current list's head's prev = bp */
        PUT(bp, 0);                             /* bp's prev = 0 */
        PUT(bp + WSIZE, (size_t)free_listp);    /* bp's next = the start of the free list */
        free_listp = bp;                        /* the freelist starts with fb */
    }
}

static void LIFO_remove(char* bp) {
    if (NEXT_FREE_BLKP(bp) == 0 && PREV_FREE_BLKP(bp) == 0) {       /* bp is the only free block */
        free_listp = 0;
    } 
    else if (NEXT_FREE_BLKP(bp) != 0 && PREV_FREE_BLKP(bp) == 0) {  /* if next exists then bp is the start of the list */
        free_listp = NEXT_FREE_BLKP(bp);                                /* Next is now the start of the list */
        PUT(NEXT_FREE_BLKP(bp), 0);                                     /* Next's prev = 0 */
    } 
    else if (NEXT_FREE_BLKP(bp) == 0 && PREV_FREE_BLKP(bp) != 0) {  /* if prev exists then pb is end of the list */
        PUT(PREV_FREE_BLKP(bp) + WSIZE, 0);                             /* Prev's next = 0 */
    }
    else {                                                          /* else bp is in the middle of the list */
        PUT(PREV_FREE_BLKP(bp) + WSIZE, (size_t)NEXT_FREE_BLKP(bp));    /* Prev's next = next */ 
        PUT(NEXT_FREE_BLKP(bp), (size_t)PREV_FREE_BLKP(bp));            /* Next's prev = prev */
    }
}


/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {             /* Case 1: Both blocks are allocated, no coalessing reqired */
        //do nothing
    }
    else if (prev_alloc && !next_alloc) {       /* Case 2: Next block is free */
        LIFO_remove(NEXT_BLKP(bp));             /* remove next block from free list */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }
    else if (!prev_alloc && next_alloc) {       /* Case 3: Previous block is free */
        LIFO_remove(PREV_BLKP(bp));             /* remove prev block from free list */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {                                      /* Case 4: Both blocks are free  */
        LIFO_remove(NEXT_BLKP(bp));             /* remove next block from free list */
        LIFO_remove(PREV_BLKP(bp));             /* remove prev block from free list */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    LIFO_insert(bp);                            /* add coalesed block to the free list */

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
    char *bp;
    for (bp = heap_prologue; GET_SIZE(HDRP(bp)); bp = NEXT_BLKP(bp)) { /* check all blocks on heap */
        if(verbose) { printblock(bp); }
        if(!checkFreeBlockIsInFreeList(bp))     { return 0; }      
        if(!checkValidBlock(bp))                { return 0; }
        if(!checkBlockOverlap(bp))              { return 0; }
        if(!checkIfTwoContinuousFreeBlocks(bp)) { return 0; }
        if(!checkIfOutOfBounds(bp))             { return 0; }
    }
    printblock(bp);
    // printf("total heap size %p:%p\n", NEXT_BLKP(heap_prologue), heap_epilogue); 
    
    /* Run through the free list */
    for (char *f_list = free_listp; f_list != 0; f_list = NEXT_FREE_BLKP(f_list)) { /* The second word in the "payload" is the pointer to the next free block */
        
        if((int)f_list & 0x7) {             /* The pointer is not 8bit alinged */
            printf("Error: the free block %p is not 8bit allinged\n", f_list);
           return 0;
        }

        if(heap_epilogue < f_list || f_list < heap_prologue) { /* The pointers in the free block point out of bounds */
            printf("Error: the free block %p points out of bounds    %p < %p || %p < %p\n", f_list, heap_epilogue, f_list,  f_list, heap_prologue);
            return 0;
        }

        if(GET_ALLOC(HDRP(f_list))) {   /* The block is alocated */
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
static int checkFreeBlockIsInFreeList(char *bp) 
{
    if(GET_ALLOC(HDRP(bp)) == 0) {      /* if block is free */
        for(char *f_list = free_listp; f_list != 0; f_list = NEXT_FREE_BLKP(f_list)) {
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
static int checkValidBlock(char *bp) 
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

static int checkBlockOverlap(char *bp) 
{
    if (FTRP(bp) > HDRP(NEXT_BLKP(bp))) {
        printf("Error: blocks %p and %p overlap\n", bp, NEXT_BLKP(bp));
        return 0;
    }
    return 1;
}

static int checkIfTwoContinuousFreeBlocks(char *bp) 
{
    if(GET_ALLOC(HDRP(bp)) == 0) { // 2 adjecent free blocks ?
        if(GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0) {
            printf("Error: block %p and %p are free adjacent blocks", PREV_BLKP(bp), bp);
            return 0;
        }
    }
    return 1;
}

static int checkIfOutOfBounds(char *bp) 
{
    if(heap_epilogue < NEXT_BLKP(bp)) { /* The pointers in the free block point out of bounds */
        printf("Error: the block %p is out of bounds: heap_epilogue:%p < NEXT_BLKP(bp):%p\n", bp, heap_epilogue, NEXT_BLKP(bp));
        return 0;
    }
    if(PREV_BLKP(bp) < heap_prologue) { /* The pointers in the free block point out of bounds */
        printf("Error: the block %p is out of bounds: PREV_BLKP(bp) < heap_prologue\n", bp);
        return 0;
    }
    return 1;
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize  = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize  = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: e: [%d:%c] EOL\n", bp, hsize, (halloc ? 'a' : 'f'));
        return;
    }

    printf("%p: h: [%d:%c] f: [%d:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}