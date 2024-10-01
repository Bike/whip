CFLAGS=-g -Wall -Wno-unused -flto -fno-strict-aliasing -fvisibility=hidden
INCLUDES=-Iwhippet/api/
LDFLAGS=-flto

COMPILE=$(CC) $(CFLAGS) $(INCLUDES)

PLATFORM=gnu-linux

gcopts := -DGC_DEBUG=1 -DGC_PRECISE_ROOTS=1 -DGC_CONSERVATIVE_ROOTS=1
collector := mmc

scheme: scheme.o gc.o gc-stack.o gc-options.o gc-platform.o gc-ephemeron.o gc-finalizer.o
	$(CC) $(LDFLAGS) -o scheme scheme.o gc.o gc-stack.o gc-options.o gc-platform.o gc-ephemeron.o gc-finalizer.o -lm # mmc needs sqrt but why on the end??

clean:
	rm -f scheme
	rm -f *.o

gc-stack.o: whippet/src/gc-stack.c
	$(COMPILE) -o gc-stack.o -c whippet/src/gc-stack.c

gc-options.o: whippet/src/gc-options.c
	$(COMPILE) -o gc-options.o -c whippet/src/gc-options.c

gc-platform.o: whippet/src/gc-platform-$(PLATFORM).c
	$(COMPILE) -o gc-platform.o -c whippet/src/gc-platform-$(PLATFORM).c

# Apparently we need these two even if we're not actually using them?
gc-ephemeron.o: embed.h whippet/src/gc-ephemeron.c
	$(COMPILE) -include embed.h -o gc-ephemeron.o -c whippet/src/gc-ephemeron.c

gc-finalizer.o: embed.h whippet/src/gc-finalizer.c
	$(COMPILE) -include embed.h -o gc-finalizer.o -c whippet/src/gc-finalizer.c

gc.o: embed.h whippet/src/$(collector).c
	$(COMPILE) $(gcopts) -include embed.h -o gc.o -c whippet/src/$(collector).c

scheme.o: scheme_whippet.c whippet/api/$(collector)-attrs.h
	$(COMPILE) $(gcopts) -include whippet/api/$(collector)-attrs.h -o scheme.o -c scheme_whippet.c
