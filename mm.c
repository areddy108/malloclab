/*
    An implementation of malloc that uses free lists that are segregated by block size.
    The implementation was built off of the textbook (implicit list) which was then turned to an explicit list
    and finally segregated free lists.

    We use the standards header and footer (4 bytes) for both free and allocated blocks found in the textbook code.
    As well as the methods associated with them that are provided by the text book.

    Methods addblock and removeblock, add and remove blocks from the seg lists.
    The seg lists are also sorted in ascending order. Malloc, free, and realloc use
    these methods to allocate and free and updated the seglists (Gloval Variable) accordingly.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 *NOTE TO STUDENTS: Before you do anything else, please
 *provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /*Team name */
    "Abhinav Reddy + Andrew Huh",
    /*First member's full name */
    "Abhinav Reddy",
    /*First member's email adderess */
    "AbhinavReddy2022@u.northwestern.edu",
    /*Second member's full name (leave blank if none) */
    "Andrew Huh",
    /*Second member's email address (leave blank if none) */
    "AndrewHuh2022@u.northwestern.edu"
};


/* alignment  must be equal to integer size */
#define ALIGNMENT 8

/*rounds up to the nearest multiple of ALIGNMENT*/
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/*Basic constants and macros*/
#define WSIZE     4
#define DSIZE     8
#define CHUNKSIZE (1<<12)
#define MINSIZE   16
#define REBUFFC  (1<<7)
#define LISTSIZE   20

/*Macro to find min and max */
#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y)) 

/*Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))

/*Read the size and allocated fields from address*/
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(ptr) ((char *)(ptr) - WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)


/* Given block ptr bp, compute address of next and previous blocks */
#define PREV(ptr) (*(char **)(ptr))
#define NEXT(ptr) (*(char **)(NEXT_PTR(ptr)))

/* Address of next and previous entries for freeblock */
#define SET(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))
#define PREV_PTR(ptr) ((char *)(ptr))
#define NEXT_PTR(ptr) ((char *)(ptr) + WSIZE)

/* Get Address of next and previous blocks */
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))

/*get size, allocation bit, tag, realloc tag from address */
#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_MTAG(p)   (GET(p) |= 0x2)
#define REMOVE_MTAG(p) (GET(p) &= ~0x2)
#define PUT_TAG(p, val) (*(unsigned int *)(p) = (val))

/* Global variable for seglists */
void *seglists[LISTSIZE];


static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void addblock(void *ptr, size_t szize);
static void removeblock(void *ptr);

/*
 * Extends the heap and also adds the new
 * free block into the correct seglist
 */
static void *extend_heap(size_t size){
    size_t tempsize=size;
    void *ptr= mem_sbrk(tempsize);
    if(ptr == (void *) -1) {
        return NULL;
    }
    PUT_TAG(HDRP(ptr),PACK(tempsize,0));
    PUT_TAG(FTRP(ptr),PACK(tempsize,0));
    PUT_TAG(HDRP(NEXT_BLKP(ptr)),PACK(0,1));
    addblock(ptr,tempsize);
    return coalesce(ptr);
}

/*
 * Iniatlize the memomory manger
 * Sets segregated free lists to to NULL
 * Checks if can allocate to heap or not (return -1)
 * Prologue header, prologue, footer, epilogue footer,
 * and allignment padding
 */
int mm_init(void){
    int i;
    for(i=0;i  < LISTSIZE; i++) {
        seglists[i] = NULL;
    }

    char *heap;
    if((long)(heap = mem_sbrk(4 *WSIZE)) == -1) {
        return -1;
    }

    PUT_TAG(heap, 0);
    PUT_TAG(heap + 1*WSIZE, PACK(DSIZE,1));
    PUT_TAG(heap + 2*WSIZE, PACK(DSIZE,1));
    PUT_TAG(heap + 3*WSIZE, PACK(0,1));

    if(extend_heap(1 << 6)==NULL)
        return -1;
    return 0;
}

/*
 * Increments the pointer to allocate a block that
 * has a size that is a multiple of the ALIGNMENT.
 * Extends (also checks if possible to expand)
 * the heap if necessary and also locates the
 * approriate free list.
 */
void *mm_malloc(size_t size){
    if(size==0) {
        return NULL;
    }

    size_t extendsize;
    void *ptr = NULL;


    size_t asize ;
    if( size <= DSIZE){
        asize = 2*DSIZE;
    }else{
        asize =ALIGN(size + DSIZE);
    }

    size_t find =asize;
    int i;
    for(i = 0; i < LISTSIZE; i++){
        if((i == LISTSIZE -1) || (find <= 1 && seglists[i] != NULL)){
            ptr = seglists[i];
            while(ptr !=NULL  && ((asize > GET_SIZE(HDRP(ptr)) || GET_TAG(ptr)))){
                ptr = PREV(ptr);
            }
            if(ptr != NULL) {
                break;
            }
        }
        find = find >> 1;
    }


    if(ptr == NULL){
        extendsize = MAX(asize,CHUNKSIZE);
        ptr = extend_heap(extendsize);
    }

    if(ptr == NULL) {
        return NULL;
    }
    ptr = place(ptr,asize);
    return ptr;
}

/*
 * Free's a block, removes tags, and adds to the
 * appropriate seg list
 */
void mm_free(void *ptr){
    size_t size= GET_SIZE(HDRP(ptr));
    REMOVE_MTAG(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    addblock(ptr,size);
    coalesce(ptr);

}

/*
 * Reallocates a block and extends the heap if needed.
 * There is a buffer given to the block to make sure that there
 * will be room for the next reallocation. Checks buffer size and gets
 * marked if not large enough which guarnatees that it can't be coalesced.
 */
void *mm_realloc(void *ptr, size_t size){
    void *oldptr = ptr;

    if(size == 0 )
        return NULL;
    size_t asize =size;
    if( size <= DSIZE){
        asize = 2*DSIZE;
    }else{
        asize =ALIGN(size + DSIZE);
    }
    asize += REBUFFC;
   
   
    int buffer = GET_SIZE(HDRP(ptr)) - asize;
    int allcposs = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - asize;
    int extendsize = MAX ( -allcposs, CHUNKSIZE);
    int free = (GET_ALLOC(HDRP(NEXT_BLKP(ptr)))==0 || GET_SIZE(HDRP(NEXT_BLKP(ptr))) == 0);

    if(buffer < 0 && free && allcposs < 0 && extend_heap(extendsize) == NULL){
        return NULL;
    }else if (buffer < 0 && free && allcposs < 0){
        allcposs = allcposs + extendsize;
    }
    
    if(buffer < 0 && free){
        removeblock(NEXT_BLKP(ptr));
        PUT_TAG(HDRP(ptr), PACK(asize + allcposs,1));
        PUT_TAG(FTRP(ptr), PACK(asize + allcposs,1));
    }else if(buffer < 0){
        oldptr = mm_malloc(asize -DSIZE);
        memcpy( oldptr, ptr, MIN(size,asize));
        mm_free(ptr);
    }

    if(buffer < 0){
        buffer = GET_SIZE(HDRP(oldptr)) - asize;
    }

    if(buffer < 2 *REBUFFC)    {
        SET_MTAG(HDRP(NEXT_BLKP(oldptr)));
    }
    return oldptr;

}


/*
 * Combines free block (new) with freeblocks next to it
 * adds new combined block to seglist
*/
static void *coalesce(void *ptr){
    size_t size =GET_SIZE(HDRP(ptr));
    size_t isnext =GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t isprev =GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t tag = GET_TAG(HDRP(PREV_BLKP(ptr)));


    if(tag  || isprev && isnext){
        return ptr;
    }else if(tag || isprev){
        removeblock(ptr);
        removeblock(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));
    }else if (isnext){
        removeblock(ptr);
        removeblock(PREV_BLKP(ptr));
        size+= GET_SIZE(HDRP(PREV_BLKP(ptr)));
        ptr= PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));
    }else{
        removeblock(ptr);
        removeblock(PREV_BLKP(ptr));
        removeblock(NEXT_BLKP(ptr));
        size+= GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        ptr = PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));
    }

    addblock(ptr,size);
    return ptr;
}

/*
 * Sets teh appropriate headers and footers for
 * new blocks that have been allcoated.
 */
static void *place(void *ptr, size_t asize){

    size_t size = GET_SIZE(HDRP(ptr));
    size_t allcposs = size - asize;

    removeblock(ptr);

    if(allcposs <=MINSIZE){
        PUT(HDRP(ptr), PACK(size,1));
        PUT(FTRP(ptr), PACK(size,1));
    }else if(asize < 100){
        PUT(HDRP(ptr), PACK(asize,1));
        PUT(FTRP(ptr), PACK(asize,1));
        PUT_TAG(HDRP(NEXT_BLKP(ptr)), PACK(allcposs,0));
        PUT_TAG(FTRP(NEXT_BLKP(ptr)), PACK(allcposs,0));
        addblock(NEXT_BLKP(ptr),allcposs);
    }else{
        PUT(HDRP(ptr), PACK(allcposs,0));
        PUT(FTRP(ptr), PACK(allcposs,0));
        PUT_TAG(HDRP(NEXT_BLKP(ptr)), PACK(asize,1));
        PUT_TAG(FTRP(NEXT_BLKP(ptr)), PACK(asize,1));
        addblock(ptr,allcposs);
        return NEXT_BLKP(ptr);
    }
    return ptr;


}

/*
 * Adds block to a seglist. Finds the correct seglist and findes location to add
 * as they lists are sorted in ascending order. Finally sets the prev and next for
 * the new block.
 */
static void addblock(void *ptr, size_t size){
    void *next = ptr;
    void *before = NULL;

    int i;
    for(i =0;i  < LISTSIZE -1 && size > 1; i++ ){
            size = size  >> 1;
    }

    next = seglists[i];
    while( next !=NULL && size < GET_SIZE(HDRP(next))){
        before = next;
        next = PREV(next);
    }

    if(next == NULL && before == NULL){
        SET(PREV_PTR(ptr),NULL);
        SET(NEXT_PTR(ptr),NULL);
        seglists[i]=ptr;
    }else if (next == NULL && before != NULL){
        SET(PREV_PTR(ptr),NULL);
        SET(NEXT_PTR(ptr), before);
        SET(PREV_PTR(before),ptr);
    }else if(next=! NULL && before == NULL ){
        SET(PREV_PTR(ptr), next);
        SET(NEXT_PTR(next), ptr);
        SET(NEXT_PTR(ptr), NULL);
        seglists[i]= ptr;
    }else if(next != NULL && before != NULL){
        SET(PREV_PTR(ptr),next);
        SET(NEXT_PTR(next), ptr);
        SET(PREV_PTR(before), ptr);
        SET(NEXT_PTR(ptr), before);
    }

    return;

}

/*
 * Removes a block from the seglist. Finds correct seglist
 * and adjusts PREV/NEXT blocks
 */
static void removeblock(void *ptr){
    int i;
    int size= GET_SIZE(HDRP(ptr));

    for(i = 0; i < LISTSIZE -1 && size > 1; i++){
        size = size >> 1;
    }

    if(PREV(ptr) != NULL && NEXT(ptr) == NULL) {
        SET(NEXT_PTR(PREV(ptr)), NULL);
        seglists[i] = PREV(ptr);
    }else if(PREV(ptr) != NULL && NEXT(ptr) != NULL) {
        SET(NEXT_PTR(PREV(ptr)) , NEXT(ptr));
        SET(PREV_PTR(NEXT(ptr)) , PREV(ptr));
    }else if (NEXT(ptr) == NULL){
        seglists[i]=NULL;
    }else{
        SET(PREV_PTR(NEXT(ptr)),NULL);
    }

    return;
}