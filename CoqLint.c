#include <stdio.h>
#include <string.h>

const int MAX_BUFF=100000;
const int MAX_STACK=100;
FILE *fpr, *fpw;
char buffer1[MAX_BUFF];
char buffer2[MAX_BUFF];
char lastQuery[15] = "first";
int stack[MAX_STACK];
int state;
int line;

int readOneSentence(char *buffer){
	int pointer = 0;
	int sentenceExit = 0;
	int comment = 0;
	while(1){
		if(fgets(buffer + pointer, MAX_BUFF - pointer, fpr) == NULL){
			if(feof(fpr)){
				return 1;
			}
			fprintf(stderr, "ERROR: Failed to read line %d\n", line);
			return -1;
		}
		line++;
		while(buffer[pointer] != 0){
			if(pointer != 0 && buffer[pointer-1] == '.' && (buffer[pointer] == ' ' || buffer[pointer] == '\n')){
				sentenceExit = 1;
			}
			if(pointer != 0 && buffer[pointer-1] == '*' && buffer[pointer] == ')'){
				comment = 1;
			}
			pointer++;
			if(pointer == MAX_BUFF - 1){
				fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
				return -1;
			}
		}
		if(sentenceExit == 1){
			break;
		}
		if(comment == 1){
			break;
		}
	}
	if(comment == 1){
		return 2;
	}
	else{
		return 0;
	}
}

//inBufferには' 'と'\n'以外が少なくとも1つ含まれる。
void fixSpaceLine(char *inBuffer, char *outBuffer){
	int p = 0, q = 0;
	while(inBuffer[p]){
		if(inBuffer[p] == ' ' || inBuffer[p] == '\n'){
			if(!(p == 0 || inBuffer[p-1] == ' ' || inBuffer[p-1] == '\n')){
				outBuffer[q++] = ' ';
			}
		}
		else{
			outBuffer[q++] = inBuffer[p];
		}
		p++;
	}
	outBuffer[q-1] = '\n';
	outBuffer[q] = 0;
}

int fixBracket(char *inBuffer, char *outBuffer){
	int p = 0, q = 0;
	while(inBuffer[p]){
		if(p != 0 && inBuffer[p-1] == ')' && inBuffer[p] != '.' && inBuffer[p] != ' ' && inBuffer[p] != ')' && inBuffer[p] != ','){
			if(q == MAX_BUFF){
				fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
				return -1;
			}
			outBuffer[q++] = ' ';
		}
		if(q == MAX_BUFF){
			fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
			return -1;
		}
		outBuffer[q++] = inBuffer[p++];
	}
	if(q == MAX_BUFF){
		fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
		return -1;
	}
	outBuffer[q] = 0;
	return 0;
}

int fixIndent(char *inBuffer, char *outBuffer){
	int p = 0, q = 0, sp = 0, depth = 0;
	while(inBuffer[p]){
		if(inBuffer[p] == '{'){
			stack[sp++] = 0;
		}
		else if(inBuffer[p] == '}'){
			sp--;
		}
		else if(strncmp(inBuffer + p, " match", 6) == 0 || strncmp(inBuffer + p, "(match", 6) == 0 || strncmp(inBuffer + p, "Inductive ", 10) == 0){
			stack[sp++] = 1;
			depth++;
		}
		else if(strncmp(inBuffer + p, " end", 4) == 0){
			sp--;
			depth--;
			if(q == MAX_BUFF){
				fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
				return -1;
			}
			outBuffer[q++] = '\n';
			int c;
			for(c=0;c<depth*2;c++){
				if(q == MAX_BUFF){
					fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
					return -1;
				}
				outBuffer[q++] = ' ';
			}
		}
		else if(inBuffer[p] == '|'){
			if(stack[sp-1] == 1){
				if(q != 0 && outBuffer[q-1] == ' '){
					q--;
				}
				if(q == MAX_BUFF){
					fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
					return -1;
				}
				outBuffer[q++] = '\n';
				int c;
				for(c=0;c<depth*2;c++){
					if(q == MAX_BUFF){
						fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
						return -1;
					}
					outBuffer[q++] = ' ';
				}
			}
		}
		if(strncmp(inBuffer + p, " end", 4) != 0){
			if(q == MAX_BUFF){
				fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
				return -1;
			}
			outBuffer[q++] = inBuffer[p];
		}
		p++;
	}
	if(q == MAX_BUFF){
		fprintf(stderr, "ERROR: MAX_BUFF is not enough in line %d\n", line);
		return -1;
	}
	outBuffer[q] = 0;
	return 0;
}

void fixComment(char *inBuffer, char *outBuffer){
	int p = 0, q = 2;
	int start = 0;
	outBuffer[0] = '(';
	outBuffer[1] = '*';
	while(inBuffer[p]){
		if(start == 1){
			outBuffer[q++] = inBuffer[p];
		}
		if(p != 0 && inBuffer[p-1] == '(' && inBuffer[p] == '*'){
			start = 1;
		}
		p++;
	}
	outBuffer[q] = 0;
}

int query(char *inBuffer){
	if(state == 0){
		if(strncmp(inBuffer, "Add", 3) == 0){
			if(!(strncmp(lastQuery, "Add", 3) == 0 || strncmp(lastQuery, "first", 5) == 0)){
				fprintf(fpw, "\n");
			}
			fputs(inBuffer, fpw);
			strcpy(lastQuery, "Add");
		}
		else if(strncmp(inBuffer, "From", 4) == 0 || strncmp(inBuffer, "Require", 7) == 0 || strncmp(inBuffer, "Local", 5) == 0){
			if(!(strncmp(lastQuery, "Require", 7) == 0 || strncmp(lastQuery, "first", 5) == 0)){
				fprintf(fpw, "\n");
			}
			fputs(inBuffer, fpw);
			strcpy(lastQuery, "Require");
		}
		else if(strncmp(inBuffer, "Section", 7) == 0 || strncmp(inBuffer, "End", 3) == 0 || strncmp(inBuffer, "Definition", 10) == 0 || strncmp(inBuffer, "Inductive", 9) == 0 || strncmp(inBuffer, "Fixpoint", 8) == 0){
			if(strncmp(lastQuery, "comment", 7) != 0){
				fprintf(fpw, "\n");
			}
			fputs(inBuffer, fpw);
			strcpy(lastQuery, "others");
		}
		else if(strncmp(inBuffer, "Lemma", 5) == 0 || strncmp(inBuffer, "Theorem", 7) == 0){
			if(strncmp(lastQuery, "comment", 7) != 0){
				fprintf(fpw, "\n");
			}
			fputs(inBuffer, fpw);
			strcpy(lastQuery, "others");
			state = 1;
		}
		else{
			fprintf(stderr, "ERROR: Unknown command in line %d\n", line);
		}
	}
	else if(state == 1){
		if(strncmp(inBuffer, "Proof", 5) != 0){
			fprintf(fpw, "Proof.\n");
		}
		fputs(inBuffer, fpw);
		if(strncmp(inBuffer, "Qed", 3) == 0){
			state = 0;
		}
		else{
			state = 2;
		}
	}
	else if(state == 2){
		fputs(inBuffer, fpw);
		if(strncmp(inBuffer, "Qed", 3) == 0){
			state = 0;
		}
	}
	return 0;
}

int main(int argc,char** argv){
	if(argc >= 2){
		if((fpr = fopen(argv[1],"r")) == NULL){
			fprintf(stderr, "ERROR: Failed to open %s\n", argv[1]);
			return 1;
		}
	}
	else{
		fpr = stdin;
	}
	if(argc >= 3){
		if((fpw = fopen(argv[2],"w")) == NULL){
			fprintf(stderr, "ERROR: Failed to open %s\n", argv[2]);
			return 1;
		}
	}
	else{
		fpw = stdout;
	}
	state = 0;
	line = 0;
	while(1){
		int s = readOneSentence(buffer1);
		if(s == 1){
			break;
		}
		if(s == 2){
			fprintf(fpw, "\n");
			fixComment(buffer1, buffer2);
			fputs(buffer2, fpw);
			strcpy(lastQuery, "comment");
			continue;
		}
		else if(s == -1){
			return 1;
		}
		fixSpaceLine(buffer1, buffer2);
		s = fixIndent(buffer2, buffer1);
		if(s == -1){
			return 1;
		}
		query(buffer1);
	}
	return 0;
}