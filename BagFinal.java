/*
 * This assignment is based on Erik Poll's assignment (Radboud University, Nijmegen).
 */

/* OpenJML Exercise: 
   
   This class implements a Bag of integers, using an array.

   Add JML specs to this class, to stop OpenJML from complaining.

   NB there may be errors in the code that you have to fix to stop 
   OpenJML from complaining, as these complaints of OpenJML 
   point to real bugs in the code. But keep changes to the code to
   a minimum of what is strictly needed. 
   Mark any changes you have made in the code with a comment,
   eg to indicate that you replaced <= by <.

   While developing your specs, it may be useful to use the keywords
      assert
   to add additional assertions in source code, to find out what 
   OpenJML can - or cannot - prove at a given program point.
   
   https://www.openjml.org/documentation/JML_Reference_Manual.pdf - pag: 141
*/ /*@ code_bigint_math */
class Bag {

    /*@ non_null @*/ int[] contents;     
    int n;

    /*@ invariant contents != null;
      @ invariant 0 <= n && n <= contents.length;
      @*/
  
    /*@ requires input != null && input.length >= 0;
      @ ensures contents != null;
      @*/
    Bag(int[] input) {
      n = input.length;
      contents = new int[n];
      arraycopy(input, 0, contents, 0, n);
    }
  
    Bag() {
      n = 0;
      contents = new int[0];
    }

    /*@ requires elt >= 0;
      @*/ 
    void removeOnce(int elt) {
      /*@ loop_invariant 0 <= i <= n && 0 <= n <= contents.length; @*/
      // BUG FIX: de [i <= n] a [i < n;]
      // Evitar un overflow en el array y hacerlo estricto
      for (int i = 0; i < n; i++) {  
        if (contents[i] == elt ) {
           n--;
           contents[i] = contents[n];
           return;
        }
      }
    }
  
    /*@ requires elt >= 0;
      @*/ 
    void removeAll(int elt) {
      /*@ loop_invariant i>=0 && i<=n && n >= 0 && n <= contents.length; @*/
      // BUG FIX: de [i <= n] a [i < n;]
      // Evitar un overflow en el array y hacerlo estricto
      for (int i = 0; i < n; i++) {
        if (contents[i] == elt ) {
           n--;
           contents[i] = contents[n];
           // BUG FIX: i= i-1;
           // Al reducir el tamanno del arreglo se tiene que reducir por fuerza
           // el tamanno de los indices para poder remover el valor del arreglo
           i= i-1;
        }
      }
    }

    /*@ requires elt >= 0;
      @ ensures 0 <= \result;
      @ pure 
      @*/ 
    int getCount(int elt) {
      int count = 0;
      /*@ loop_invariant i>=0 && i<=n;
        @ loop_invariant count >= 0;
        @*/
      // BUG FIX: de [i <= n] a [i < n;]
      // Evitar un overflow en el array y hacerlo estricto
      for (int i = 0; i < n; i++) 
        if (contents[i] == elt) count++; 
      return count;
    }
  
    /* Warning: you may have a hard time checking the method "add" below.
       OpenJML may warn about a very subtle bug that can be hard to spot. 
       If you cannot find the problem after staring at the code for an hour, 
       feel free to stop.
     */

    /*@ assignable \everything;
      @ requires elt >= 0;
      @*/
    void add(int elt) {
      if (n == contents.length) {
         // BUG FIX: de [2*n] a [2*n+1] 
         // Esto por que n contiene la cantidad del largo de un array en cantidad de
         // objetos mas el que se agrega que necesita ser tomado en cuenta en el arreglo
         int[] new_contents = new int[2*this.n+1]; 
         /*@ assert new_contents.length == 2*n+1;
           @ assert 0 <= n < 2*n+1;
           @ assert n < new_contents.length;
           @*/
         arraycopy(contents, 0, new_contents, 0, n);
         contents = new_contents;
      }
      contents[n]=elt;
      n++;
    }

    /*@ assignable this.contents;
      @ requires b != null;
      @*/
    void add(Bag b) {
      int[] new_contents = new int[n + b.n];
      arraycopy(contents, 0, new_contents, 0, n);
      // BUG FIX: de [n+1] a [n]
      // La operacion de n+1 produce el siguiente error: Exception in thread... 
      // java.lang.ArrayIndexOutOfBoundsException: Index 13 out of bounds for length 13
      // Al sumar n+1 se sale de los limites del array
      arraycopy(b.contents, 0, new_contents, n, b.n); 
      contents = new_contents; 
    }

    /* COMENTARIO DE ESTUDIANTES: 
    Metodo comentado por los siguientes motivos: 
     * #1 NUNCA se llama en la clase
     * #2 Metodo privado (cuando no se tiene el access modifier es por default private)
     *
    void add(int[] a) {
      this.add(new Bag(a));
    }*/
    
    /*@ requires b != null; 
      @ requires b.contents != null;
      @*/
    Bag(Bag b) {
      // BUG FIX: set [this.contents = new int[0]]
      // Nunca se inicializa el array y se ocupa inicializar cuando se crea la clase
      this.contents = new int[0];
      this.add(b); 
    }    
 
    /*@ assignable dest[*];
      @ requires src != null;
      @ requires 0 <= length;
      @ requires 0 <= srcOff && (srcOff + length) <= src.length;
      @ requires 0 <= destOff && (destOff + length) <= dest.length;
      @ requires dest != null;
      @ ensures dest != null && dest.length == \old(dest.length);
      @ ensures length == \old(length) ==> 0 <= length;
      @ ensures n == \old(n);
      @ ensures contents == \old(contents);
      @*/
    private void arraycopy(int[] src,
                           int   srcOff,
                           int[] dest,
                           int   destOff,
                           int   length) {
      /*@ loop_invariant 0 <= destOff+i;
        @ loop_invariant 0 <= srcOff+i;
        @ loop_invariant 0 <= length;
        @ loop_invariant 0 <= i <=length; 
        @*/
        for( int i=0 ; i<length; i++) {
         dest[destOff+i] = src[srcOff+i];
      }
    }
    
  }
