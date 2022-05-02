#include <time.h>
#include <sys/time.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h> 
#include <sys/socket.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include <pthread.h>
#include <ctype.h>

/* 

   The cinterf.h file (from the XSB code base, see http://xsb.sourceforge.net/api/dir_C_3A_2Fdev_2Fsandbox_2Fxsb_5Frelease_2FXSB_2Femu_2F.html) 
   contains prototypes for various functions exposed by the XSB<-->C API. 

 */

#include "cinterf.h"

#include "varstring_xsb.h"

extern char *xsb_executable_full_path(char *);

extern char *strip_names_from_path(char*, int);

/* context.h is necessary for the type of a thread context. */

#include "context.h"

/* 

If all goes well, athena.h should contain C prototypes for 
all SML functions that are to be called from C.

*/


#include "athena.h"

#define END_OF_STRING '\0'

#define answer_separator '|'

#define QUERY_TIMEOUT_IN_SECONDS 1800

int max_query_results = 1000;

int sotar_client_request_done = 0;

typedef struct node *nodeptr;

typedef struct node {
  char* word;
  int count;
  nodeptr next;
} node;

/*

K.A.: Some hand-rolled rudimentary hash-table code in order
to weed out duplicate query answers. 
 
 */

#define DISTINCT_ANSWER_HT_SIZE 1171
#define HASH_MULT 31

unsigned int quickHash(char* p){
  unsigned int h = 0;
  for ( ; *p; p++) 
    h = HASH_MULT * h + *p;
  return h % DISTINCT_ANSWER_HT_SIZE;
}

void initHT(nodeptr *ht){
  int i;
  for (i = 0; i < DISTINCT_ANSWER_HT_SIZE; ++i)
    ht[i] = NULL;
}

int alreadySeen(nodeptr *hash_table, char* str){
  unsigned int hash_code = quickHash(str);
  nodeptr p;
  for (p = hash_table[hash_code]; p  != NULL; p = p->next) 
    if (strcmp(str,p->word) == 0) {
      (p->count)++;
      return 1;
    }
  p = (nodeptr) malloc(sizeof(node));
  p->count = 1;
  p->word = (char*) malloc(strlen(str)+1);
  strcpy(p->word,str);
  p->next = hash_table[hash_code];
  hash_table[hash_code] = p;
  return 0;
}

void destroyHT(nodeptr *hash_table){
  int i;
  nodeptr p;
  for (i = 0; i < DISTINCT_ANSWER_HT_SIZE; ++i) {
    for (p = hash_table[i]; p  != NULL; p = p->next) {
      free(p->word);
      free(p);
    }
  }
}

void freeIntermediate(char**,int); 

/* 

KA: The above is a prototype for the function that does systematic freeing of all the memory that 
is allocated for answering queries. Note that this does not free the actual bytes for the ultimate
answer - that has to be done from within SML, after the answer has been consumed. Rather, this only 
frees intermediate resources allocated during the execution of answerQuery below.

*/


int isQuery(int); /* function prototype */

void error(const char *msg)
{
    perror(msg);
    exit(1);
}
 
int initXSB()
{
  char init_string[MAXPATHLEN];
  char* xsbHome = getenv("XSB_HOME");
  if (xsbHome == NULL) {
    fprintf(stderr,"Missing environmental variable XSB_HOME.");
    exit(XSB_ERROR);
  }
  printf("XSB_HOME set to %s\n", xsbHome);
  strcpy(init_string, xsbHome);

  if (xsb_init_string(init_string)) {
    fprintf(stderr,"%s Initializing reasoning engine: %s\n",xsb_get_init_error_type(),
	    xsb_get_init_error_message());
    exit(XSB_ERROR);
  }
  printf("\nXSB's reasoning engine was properly initialized and integrated with Athena...\n");
  return 0;
}

void reInitializeXSB(){
  xsb_close(CTXT);     
  initXSB();
}

void makeFinalAnswer(char** final_answer,char** answer_array,int answer_count,int total_char_count) {
  int total = 1 + total_char_count + answer_count;
  *final_answer = (char*) malloc(total); 
  int offset = 0;
  int i;
  for (i = 0; i < answer_count; ++i) {
    char* str = answer_array[i];
    strcpy((*final_answer) + offset,str);
    offset = offset + strlen(str);
    strcpy((*final_answer) + offset,"\n");
    offset = offset + 1;
  }
}

void freeIntermediate(char** answer_array,int answer_count){
  int i;
  for (i = 0; i < answer_count; ++i) 
    free(answer_array[i]);
}

char* answerQuery(char* goal, int max_query_results) {
  //  printf("\nAbout to issue the following translated query: %s", goal);
  if (strlen(goal) < 1) 
    return NULL;
  XSB_StrDefine(return_string);
  int answer_count = 0;
  int total_char_count = 0;
  int limit;
  if (max_query_results <= 0)
    limit = 1000000;
  else
    limit = max_query_results;
  char** answer_array = (char**) malloc(limit * sizeof(char*));
  if (answer_array == NULL) 
    printf("\nMalloc on answer_array failed.\n");
  //  if (answer_array != NULL) 
  //    printf("\nmalloc on answer_array succeeded.\n");

  int rc, at_least_one = 0;

  rc = xsb_query_string_string(CTXTc goal,&return_string,"|");

  if (rc == XSB_ERROR)  {
    free(answer_array);
    char* final_answer = (char*) malloc(2000 * sizeof(char));
    sprintf(final_answer,"!Query Error: %s/%s\n",xsb_get_error_type(CTXT),xsb_get_error_message(CTXT));
    return final_answer;
  }
  if (rc != XSB_SUCCESS) {
    free(answer_array);
    char* final_answer = (char*) malloc(1 + sizeof(char));
    strcpy(final_answer,"%");
    return final_answer;
  }
  at_least_one = 1;
  while ((rc == XSB_SUCCESS) && (answer_count < limit)) {
    char* answer = return_string.string;
    int new_answer_len  = strlen(answer);
    total_char_count = total_char_count + new_answer_len;
    char* new_answer  = (char*) malloc(1 + (new_answer_len * sizeof(char)));
    strcpy(new_answer,answer);
    answer_array[answer_count] = new_answer;       
    answer_count += 1;
    rc = xsb_next_string(CTXTc &return_string,"|");
  }
  if (at_least_one) {
    xsb_close_query();
  }
  if (rc == XSB_ERROR) 
    fprintf(stderr,"++Query Error: %s/%s\n",xsb_get_error_type(CTXT),xsb_get_error_message(CTXT));
  char* final_answer; 
  makeFinalAnswer(&final_answer,answer_array,answer_count,total_char_count); 
  freeIntermediate(answer_array,answer_count);
  free(answer_array);
  return final_answer;
}

char* mallocChars(int i){
  return (char*) malloc(i * sizeof(char));
}

char* doXSBCommand(char* command){ 
  char* res = (char*) malloc(300 * sizeof(char));
  if (xsb_command_string(CTXTc command) == XSB_ERROR)  
    sprintf(res,"!ERROR: %s/%s\n",xsb_get_error_type(CTXT),xsb_get_error_message(CTXT));
  else 
    strcpy(res,"OK");
  return res;
}
