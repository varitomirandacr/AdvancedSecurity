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
  
*/
//https://stackoverflow.com/questions/65274277/jml-remove-warning-after-calling-a-function
//https://stackoverflow.com/questions/65291445/why-openjml-can-not-prove-an-assertion-in-for-cycle

/* https://www.openjml.org/documentation/JML_Reference_Manual.pdf - pag: 141 */
/* code_java_math */ // Testeado pero no usado
/* code_safe_math */ // Testeado pero no usado
/*@ code_bigint_math */ // Testeado y funciono
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


    //@ ensures \result >= 0;
    /*@ pure @*/ int getCount(int elt) {
      int count = 0;
      //@ loop_invariant i>=0 && i<=n;
      //@ loop_invariant count >= 0;
      for (int i = 0; i < n; i++) // remove <= por < para evitar overflow
        if (contents[i] == elt) count++; 
      return count;
    }
  

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

    /* COMENTARIO DE ESTUDIANTES: 
    Metodo comentado por los siguientes motivos: 
     * #1 NUNCA se llama en la clase
     * #2 Metodo privado (cuando no se tiene el access modifier es por default private)
     *
    void add(int[] a) {
        this.add(new Bag(a));
    }*/
    
    /*
    //@ requires b != null;
    Bag(Bag b) {
        contents = new int[0]; 
        n = 0;
        this.add(b); 
    }*/

    //@ requires b != null;
    //@ modifies n,contents; // Linea 102 n+1 ???
    void add(Bag b) {
      int[] new_contents = new int[n+b.n];
      arraycopy(this.contents, 0, new_contents, 0, n);
      arraycopy(b.contents, 0, new_contents, n, b.n); 
      contents = new_contents; 
      n = n + b.n;
    }
 
    //@ requires src != null;
    //@ requires srcOff >=0;
    //@ requires dest != null;
    //@ requires destOff >=0;
    //@ requires length >=0;
    //@ requires srcOff + length <= src.length;
    //@ requires destOff + length <= dest.length;
    //@ assignable dest[*];
    //@ ensures dest.length == \old(dest.length);
    //@ ensures length == \old(length) ==> length >= 0;
    //@ ensures dest != null;
    //@ ensures n == \old(n);
    //@ ensures contents == \old(contents);
    private void arraycopy(int[] src,
                                  int   srcOff,
                                  int[] dest,
                                  int   destOff,
                                  int   length) {
      //@ loop_invariant destOff+i >= 0;
      //@ loop_invariant srcOff+i >= 0;
      //@ loop_invariant length >= 0;
      /*@ loop_invariant i>=0 && i<=length; @*/
      for( int i=0 ; i<length; i++) {
         dest[destOff+i] = src[srcOff+i];
      }
    }
    
  }
