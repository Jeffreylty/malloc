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
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "czou3+tliu31",
    /* First member's full name */
    "Canruo Zou",
    /* First member's email address */
    "czou3@u.rochester.edu",
    /* Second member's full name (leave blank if none) */
    "Tianyi Liu",
    /* Second member's email address (leave blank if none) */
    "tliu31@u.rochester.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1<<12)   /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Pointer of free block's next and pre block in free list */
#define PREV(bp) (*(char **)(bp))
#define NEXT(bp) (*(char **)(NEXT_PTR(bp)))

/* Address stored in the free block's next and pre block*/
#define PREV_PTR(bp)  ((char *)(bp))
#define NEXT_PTR(bp)  ((char *)(bp) + WSIZE)

/* Set the value stored in p into ptr */
#define PUT_PTR(p, ptr) (*(unsigned int *)p = (unsigned int )ptr )

#define MAX_list 32

/* Variables */
void * heap_listp;
void **free_list;   /* List of free pointer */

/*Functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t size);
static void insert(void *bp, size_t size);
static void delete(void *bp);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Initialize the segregated free list, and set every entries into NULL */
    free_list = mem_sbrk(MAX_list*WSIZE);
    for (int i = 0; i < MAX_list; i++){
        free_list[i] = NULL;
    }
    
    /* Creat the initial empty heap */
    heap_listp = mem_sbrk(4*WSIZE);
    if( heap_listp == (void *)-1)
        return -1;
    
    PUT(heap_listp,0); /* Alignment padding*/
    PUT(heap_listp + (1*WSIZE),PACK(DSIZE,1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE),PACK(DSIZE,1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE),PACK(0,1)); /* Epilogue header */
    heap_listp += (2*WSIZE);
    

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/* Extends the heap with a new free block */
static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment*/
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* Free block header */
    
    /* Add this free block into the segregated free list. */
    insert(bp, size);
    
    /* Coalesce if the previous block was free*/
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
//    int newsize = ALIGN(size + SIZE_T_SIZE);
//    void *p = mem_sbrk(newsize);
//    if (p == (void *)-1)
//    return NULL;
//    else {
//        *(size_t *)p = size;
//        return (void *)((char *)p + SIZE_T_SIZE);
//    }
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit*/
    char *bp;
    
    /* Ignore spurious requests */
    if(size == 0){
        return NULL;
    }
    
    /* Adjust block size to include overhead and alignment reqs */
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    }else{
        asize = DSIZE * ((size +(DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp,asize);
        return bp;
    }
    /* No fit found. Get more menmory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize)) == NULL) {
        return NULL;
    }
    place(bp,asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    
    PUT(HDRP(ptr),PACK(size,0));
    PUT(FTRP(ptr),PACK(size,0));
    /* Put the freed blcok into the segregated free list*/
    insert(ptr, size);
    coalesce(ptr);
}

static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) {
        return bp;
    }
    
    else if(prev_alloc && !next_alloc){
        delete(bp);
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp),PACK(size, 0));
        PUT(FTRP(bp),PACK(size, 0));
    }
    
    else if(!prev_alloc && next_alloc){
        delete(bp);
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp),PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    else{
        delete(bp);
        delete(NEXT_BLKP(bp));
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)),PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t asize = size;    /* Size of new block */
    void *newptr = ptr;        /* Ptr to the result block */
    
    // If size == 0 then this is just free, and we return NULL
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    
    // If oldptr is NULL, then this is just malloc
    if(ptr == NULL) {
        return mm_malloc(size);
    }
    
    // Adjust block size to include overhead and alignment reqs
    if (asize <= DSIZE) {
        asize = 2 * DSIZE;
    }else {
        asize = ALIGN(size + DSIZE);
    }
    
    // Return the original ptr if size is less than the original
    if (GET_SIZE(HDRP(ptr)) >= size) {
        return ptr;
        // When next block is free or is end
    }else if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
        // Need extend the block
        int diff = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - size;
        if(diff < 0) {
            if (extend_heap(MAX(-diff, 1<<12)) == NULL)   return NULL;
            diff += MAX(-diff, 1<<12);
        }
        
        delete(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(asize + diff, 1));
        PUT(FTRP(ptr), PACK(asize + diff, 1));
        // Use new free block
    }else {
        newptr = mm_malloc(asize);
        memcpy(newptr, ptr, GET_SIZE(HDRP(ptr)));
        mm_free(ptr);
    }
    
    return newptr;
}

/* place the requested block at the beginning of the free block, splitting only if the size of the remainder would equal or exceed the mini- mum block size. */
static void place(void *bp, size_t size){
    delete(bp);
    size_t temp = GET_SIZE(HDRP(bp));
    
    if((temp - size) < 2 * DSIZE){
        PUT(HDRP(bp), PACK(temp, 1));
        PUT(FTRP(bp), PACK(temp, 1));
    }else{
        PUT(HDRP(NEXT_BLKP(bp)),PACK((temp - size), 0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK((temp - size), 0));
        PUT(HDRP(bp),PACK(size, 1));
        PUT(FTRP(bp),PACK(size, 1));
        insert(NEXT_BLKP(bp), (temp - size));
    }
}

/* Add the free block to the free list */
static void insert(void *bp, size_t size){
    int pos = 0;
    size_t temp = size;
    void *cur = bp;
    void *pre = NULL;
    
    // select the correct list to insert the block
    while (pos < MAX_list -1 && temp > 1){
        temp = temp >> 1;
        pos ++;
    }
    
    // find the correct place to insert the block
    cur = free_list[pos];
    while (cur != NULL && size > GET_SIZE(HDRP(cur))) {
        pre = cur;
        cur = NEXT(cur);
    }
    
    if (cur != NULL && pre == NULL) {
        PUT_PTR(PREV_PTR(bp), NULL);
        PUT_PTR(NEXT_PTR(bp), cur);
        PUT_PTR(PREV_PTR(cur), bp);
        free_list[pos]= bp;
    }else if(cur ==NULL && pre == NULL){
        PUT_PTR(NEXT_PTR(bp),NULL);
        PUT_PTR(PREV_PTR(bp),NULL);
        free_list[pos]= bp;
    }else if(cur ==NULL && pre != NULL){
        PUT_PTR(NEXT_PTR(pre),bp);
        PUT_PTR(PREV_PTR(bp),pre);
        PUT_PTR(NEXT_PTR(bp),NULL);
    }else{
        PUT_PTR(NEXT_PTR(bp),cur);
        PUT_PTR(PREV_PTR(cur),bp);
        PUT_PTR(PREV_PTR(bp),pre);
        PUT_PTR(NEXT_PTR(pre),bp);
    }
}

/* Delete the block from free block list */
static void delete(void *bp){
    int pos = 0;
    size_t temp = GET_SIZE(HDRP(bp));
    
    while (pos < MAX_list -1 && temp > 1){
        temp = temp >> 1;
        pos ++;
    }
    
    if(PREV(bp) != NULL && NEXT(bp) != NULL){
        PUT_PTR(NEXT_PTR(PREV(bp)),NEXT(bp));
        PUT_PTR(PREV_PTR(NEXT(bp)),PREV(bp));
    }else if(PREV(bp) == NULL && NEXT(bp) != NULL){
        PUT_PTR(PREV_PTR(NEXT(bp)),NULL);
        free_list[pos] = NEXT(bp);
    }else if(PREV(bp) != NULL && NEXT(bp) == NULL){
        PUT_PTR(NEXT_PTR(PREV(bp)),NULL);
    }else{
         free_list[pos] = NULL;
    }
}

static void *find_fit(size_t asize){
    int pos = 0;
    size_t temp = asize;
    void *cur = NULL;
    
    while (pos < MAX_list -1){
        if((pos == MAX_list -1) || ((temp <=1 ) && (free_list[pos] != NULL)){
            cur = free_list[pos];
            while((cur != NULL) && ((asize > GET_SIZE(HDRP(cur))))){
                            cur = NEXT(cur);
            }
            if(cur != NULL)
                break;
        }
           temp >>=1;
           pos++;

    }

           return pos;
}












