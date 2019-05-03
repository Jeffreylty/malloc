/*
 * In our mm approach, a block has a following structure
 *      
 *      |    head     |
 *      ———————
 *      |   payload   |
 *      ———————
 *      |   padding   |
 *      ———————
 *      |    foot     |
 *
 *  The free list is a set of double linked lists, sorted by the 
 *  size of the block, with a following structure
 *     ———————————————————————
 *     |  |  |  |  |  |  |  |  |
 *     ———————————————————————
 *      /\ /\ /\
 *      |  |  |
 *      \/ \/ \/
 *      ——
 *     |  |
 *      ——
 *      /\ 
 *      |
 *      \/
 *      ——
 *     |  |
 *      ——
 *
 *  Whenever we freed a block or extend the heap, we insert it into segregated free list;
 *  Whenever we try to allocate a memory of size n, we traverse the free list,
 *  find a free block and delete it from the free list.
 * 
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
#define MIN(x, y) ((x) < (y) ? (x) : (y))

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
#define NEXT(bp) (*(char **)(bp))
#define PREV(bp) (*(char **)(PREV_PTR(bp)))

/* Address stored in the free block's next and pre block*/
#define NEXT_PTR(bp)  ((char *)(bp))
#define PREV_PTR(bp)  ((char *)(bp) + WSIZE)

/* Set the value stored in p into ptr */
#define PUT_PTR(p, ptr) (*(unsigned int *)p = (unsigned int )ptr )

#define MAX_list 20

/* Variables */
void * heap_listp;	/* Head pointer of the heap */
void **free_list;   /* List of free pointer */

/*Functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t size);
static void insert(void *bp, size_t size);
static void delete(void *bp);
static int mm_check(void);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    /* Initialize the segregated free list, and set every entries into NULL */
    free_list = mem_sbrk(MAX_list * WSIZE);
    for (int i = 0; i < MAX_list; i++) {
        free_list[i] = NULL;
    }
    
    /* Creat the initial empty heap */
    heap_listp = mem_sbrk(4 * WSIZE);
    if(heap_listp == (void*) - 1)
        return -1;
    
    PUT(heap_listp, 0); /* Alignment padding*/
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE,1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE,1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2 * WSIZE);
    

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * extend_heap - Extends the heap with a new free block.
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment*/
    size = ALIGN(words);
    if((long)(bp = mem_sbrk(size)) == -1) {
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
 *     Always allocate a block whose size is a multiple of the alignm`ent.
 */
void *mm_malloc(size_t size) {

    size_t asize= size; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit*/
    void *bp = NULL;
    
    /* Ignore spurious requests */
    if(size == 0) {
        return NULL;
    }
    
    /* Adjust block size to include overhead and alignment reqs */
    if(size <= DSIZE) {
        asize = 2 * DSIZE;
    }else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }
    
    /* Search the free list for a fit */
    if((bp = find_fit(asize)) != NULL) {
        bp = place(bp, asize);
        return bp;
    }
    
    /* No fit found. Get more menmory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize)) == NULL) {
        return NULL;
    }
    bp = place(bp, asize);
  
	  //mm_check();
    return bp;
}

/*
 * mm_free - Freeing a block and put to segregated free list.
 */
void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));
    
    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    /* Put the freed blcok into the segregated free list*/
    insert(ptr, size);
    coalesce(ptr);
	//mm_check();
}

/*
 * coalesce - merge the block with any adjacent free blocks.
 */
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); //size of previous free block
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); //size of next free block
    size_t size = GET_SIZE(HDRP(bp));
    
    if(prev_alloc && next_alloc) { /* case1 */
    	/*previous and next are both allocated, do nothing*/
        return bp;
    }else if(prev_alloc && !next_alloc) { /* case2 */
    	/* Delete the current block and the next blcok from the free list, and coalease them together. */
        delete(bp);
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }else if(!prev_alloc && next_alloc) { /* case3 */
    	/* Delete the current block and the previous blcok from the free list, and coalease them 				together. */
        delete(bp);
        delete(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }else { /* case4 */
    	/* Delete the current block, the next blcok, and the previous block from the free list, and coalease them together. */
        delete(bp);
        delete(PREV_BLKP(bp));
        delete(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    insert(bp, size);
	  //mm_check();
    return bp;
}

/*
 * mm_realloc - Implemented in terms of mm_malloc and mm_free.
 */
void *mm_realloc(void *ptr, size_t size) {
    size_t asize = size;    /* Size of new block */
    void *newptr = ptr;        /* Ptr to the result block */
    
    // If size == 0 then return NULL
    if(size == 0)
        return NULL;

	  // If oldptr is NULL, then this is just malloc
    if(ptr == NULL)
        return mm_malloc(size);
    
    // Adjust block size to align with the new size
    if(asize <= DSIZE) {
        asize = 2 * DSIZE;
    }else {
        asize = ALIGN(size + DSIZE);
    }
 

    // Return the original ptr if size is less than the original
    if(GET_SIZE(HDRP(ptr)) >= asize) {
        return ptr;
        // When next block is free or is end
    }else if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
        int diff = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - asize;
        // If the next bolck is the end or till less than the space we need, then extend the heap
        if(diff < 0) {
            if (extend_heap(MAX(-diff, CHUNKSIZE)) == NULL) return NULL;
            diff += MAX(-diff, CHUNKSIZE);
        }
        //Occupied the next block 
        delete(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(asize + diff, 1));
        PUT(FTRP(ptr), PACK(asize + diff, 1));
        
    }else { // Use new malloced free block and copy the content from old block to new block.
        newptr = mm_malloc(asize-DSIZE);
        memcpy(newptr, ptr, GET_SIZE(HDRP(ptr)));
        mm_free(ptr);
    }
    //mm_check();
    return newptr;
}

/* 
 * place - Place the requested block at the beginning of the free block, splitting only if the size of  
 *         the remainder would equal or exceed the minimum block size. 
 */
static void *place(void *bp, size_t size) {

    size_t temp = GET_SIZE(HDRP(bp));
    delete(bp);
    size_t diff =(temp - size);
    
    if(diff < 2 * DSIZE) {
        PUT(HDRP(bp), PACK(temp, 1));
        PUT(FTRP(bp), PACK(temp, 1));
		return bp;
    }else if(size >= 32) { // this part is to optimize the external esgmentation
  		/* Put the big block in the back and small in the front to avoid external esgmentation. */
        PUT(HDRP(bp), PACK(diff, 0));
        PUT(FTRP(bp), PACK(diff, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(size, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 1));
        insert(bp, diff);
        return NEXT_BLKP(bp);
    }else {
        PUT(HDRP(bp),PACK(size, 1));
        PUT(FTRP(bp),PACK(size, 1));
        PUT(HDRP(NEXT_BLKP(bp)),PACK(diff, 0));
        PUT(FTRP(NEXT_BLKP(bp)),PACK(diff, 0));
		// Put the remaining block into free block list.
        insert(NEXT_BLKP(bp), diff);
	return bp;
    }
}

/*
 * insert - Add the free block to the free list.
 */
static void insert(void *bp, size_t size) {
    int pos = 0;
    size_t temp = size;
    void *cur = bp;
    void *pre = NULL;
    
    // select the correct list to insert the block from the size of the block.
    while(pos < MAX_list -1 && temp > 1) {
        temp = temp >> 1;
        pos ++;
    }
    
    // find the correct place in the list to insert the block with size_t size.
    cur = free_list[pos];
    while(cur != NULL && size > GET_SIZE(HDRP(cur))) {
        pre = cur;
        cur = NEXT(cur);
    }
    
    if(cur != NULL && pre == NULL) { 
	// insert in the head of the list
        PUT_PTR(PREV_PTR(bp), NULL);
        PUT_PTR(NEXT_PTR(bp), cur);
        PUT_PTR(PREV_PTR(cur), bp);
        free_list[pos] = bp;
    }else if(cur ==NULL && pre == NULL) {
	// insert if the list is empty
        PUT_PTR(NEXT_PTR(bp), NULL);
        PUT_PTR(PREV_PTR(bp), NULL);
        free_list[pos] = bp;
    }else if(cur == NULL && pre != NULL) {
	// insert in the end of the list
        PUT_PTR(NEXT_PTR(pre), bp);
        PUT_PTR(PREV_PTR(bp), pre);
        PUT_PTR(NEXT_PTR(bp), NULL);
    }else {
	// insert in the middle of the list
        PUT_PTR(NEXT_PTR(bp), cur);
        PUT_PTR(PREV_PTR(cur), bp);
        PUT_PTR(PREV_PTR(bp), pre);
        PUT_PTR(NEXT_PTR(pre), bp);
    }
}

/*
 * delete - Delete the block from free block list.
 */
static void delete(void *bp) {
    int pos = 0;
    size_t temp = GET_SIZE(HDRP(bp));
    
    // select the correct list of the block bp.
    while(pos < MAX_list -1 && temp > 1) {
        temp = temp >> 1;
        pos ++;
    }
    
    /* find the place of block bp in the list, and perform double linklist delete operation. */
    if(PREV(bp) != NULL && NEXT(bp) != NULL){ 
        PUT_PTR(NEXT_PTR(PREV(bp)), NEXT(bp));
        PUT_PTR(PREV_PTR(NEXT(bp)), PREV(bp));
    }else if(PREV(bp) == NULL && NEXT(bp) != NULL) {
        PUT_PTR(PREV_PTR(NEXT(bp)), NULL);
        free_list[pos] = NEXT(bp);
    }else if(PREV(bp) != NULL && NEXT(bp) == NULL) {
        PUT_PTR(NEXT_PTR(PREV(bp)), NULL);
    }else {
        free_list[pos] = NULL;
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes. 
 */
static void *find_fit(size_t asize) {
    int pos = 0;
    size_t temp = asize;
    void *cur;
	// select the correct list for size_t asize.
    while(pos < MAX_list -1 && temp > 1) {
        temp = temp >> 1;
        pos ++;
    }
    
    /* If cannot fit in the current list, then increment the list. */
    for(; pos < MAX_list; pos++) {
        cur = free_list[pos];
        //finding a fitted free block
        while( cur != NULL && asize > GET_SIZE(HDRP(cur))) {
	    	cur = NEXT(cur);
        }
        //until find a suitable free block
        if(cur != NULL) {
            break;
        }
    }
    return cur;
}

/* 
 * mm_check - Check the consistency of the free list and the heap.
	We cecked the following:
    Is every block in the free list marked as free? 
    Are there any contiguous free blocks that somehow escaped coalescing? 
    Is every free block actually in the free list? 
    Do the pointers in the free list point to valid free blocks? 
    Do any allocated blocks overlap? 
    Do the pointers in a heap block point to valid heap addresses?  
 */
static int mm_check() {
	void * ptr ,*ptr2;
	int count1 = 0; // count the number of free block in heap
	int count2 = 0; // count the number of ree block in free list
 	for(ptr = heap_listp; GET_SIZE(HDRP(ptr))>0 ; ptr = NEXT_BLKP(ptr) ){
		if(GET_SIZE(HDRP(ptr))!= GET_SIZE(FTRP(ptr)) || GET_ALLOC(HDRP(ptr))!= GET_ALLOC(FTRP(ptr))){
			printf("WARNING: Inconsistent header and footer\n");
			return 0;
		}
		if(!GET_ALLOC(HDRP(ptr))) count1++;

		if(HDRP(ptr) + GET_SIZE(HDRP(ptr)) -1 >= HDRP(NEXT_BLKP(ptr))){
		printf("WARNING: Payload overlaps another payload\n");
		return 0;
		}
	}

	for(int i=0 ;i<MAX_list; i++) {
        ptr2 = free_list[i];
        while (ptr2 != NULL) {
            if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr2))) || !GET_ALLOC(HDRP(PREV_BLKP(ptr2)))) {
                printf("WARNING: Contiguous free blocks that somehow escaped coalescing\n");
                return 0;
            }
            if(GET_ALLOC(HDRP(ptr2))) {
                printf("WARNING: An block in the free list marked as non free\n");
                return 0;
            }
            count2 ++;
            ptr2 = NEXT(ptr2);
        }
    }

	if(count2 != count1) {
		printf("WARNING: Not every free block actually in the free list\n");
		return 0;
	}
		return 1;
}