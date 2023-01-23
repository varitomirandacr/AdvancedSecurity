
public class Amount{

    //@ spec_public
    private int cents;    
    //@ spec_public
    private int euros;
   
    /*@ ensures this.euros == euros && this.cents == cents;
      @ ensures euros >= Integer.MIN_VALUE && euros <= Integer.MAX_VALUE;
      @ ensures cents >= Integer.MIN_VALUE && cents <= Integer.MAX_VALUE;
      @*/
    public Amount(int euros, int cents){
      this.euros = euros;
      this.cents = cents;
    }

    /*@ requires cents >= 0;
      @ requires euros >= 0;
      @ ensures \result != null;
      @ ensures Integer.MIN_VALUE < \result.euros <= 0;
      @ ensures Integer.MIN_VALUE < \result.cents <= 0;
      @*/
    public /*@ non_null @*/ Amount negate(){
      // BUG FIX: (-cents, -euros) a (-euros, -cents)
      // Valores invertidos el ctor pide primero los euros y luego los cents
      return new Amount(-euros, -cents);
    }    
    
    /* requires a != null;
      @ requires cents >= 0;
      @ requires euros >= 0;
       /requires a.euros > 0 && a.cents > 0;
       /requires this.euros > a.euros;
      @ ensures \result != null;
      @
    public testAmount subtract(testAmount a){
      return this.add(a.negate());
    }*/

    /*@ requires a != null;
      @ requires Integer.MIN_VALUE <= this.euros <= Integer.MAX_VALUE;
      @ requires Integer.MIN_VALUE <= this.cents <= Integer.MAX_VALUE;
      @ requires Integer.MIN_VALUE < (this.euros + a.euros) < Integer.MAX_VALUE;
      @ requires Integer.MIN_VALUE < (this.cents + a.cents) < Integer.MAX_VALUE;
      @ ensures \result != null;
      @*/
    public Amount add(/*@non_null@*/Amount a){
      int new_euros = euros + a.euros; 
      //@ assert Integer.MIN_VALUE < (new_euros) < Integer.MAX_VALUE;
      int new_cents = cents + a.cents; 
      //@ assert Integer.MIN_VALUE < (new_cents) < Integer.MAX_VALUE;

      // BUG FIX: de [< a <=]
      // Si no se incluye el = evaluaria hasta -99
      if (new_cents <= -100) {  
        new_cents = new_cents + 100;
        new_euros = new_euros - 1;
        //@ assert new_cents <= 100;
        //@ assert Integer.MIN_VALUE <= new_euros;
      } 
      // BUG FIX: de [> a >=]
      // Si no se incluye el = evaluaria hasta 99, caso contrario al de arriba
      if (new_cents >= 100) {  
        new_cents = new_cents - 100;
        // BUG FIX: de [- a +]
        // Cuando tenemos mas cents se restan los cents pero se deben incrementar los euros
        new_euros = new_euros + 1;
        //@ assert new_cents >= -100;
        //@ assert Integer.MAX_VALUE >= new_euros;
      } 
      if (new_cents < 0 && new_euros > 0) { 
        new_cents = new_cents + 100; 
        new_euros = new_euros - 1;
        //@ assert new_cents <= 100;
        //@ assert Integer.MIN_VALUE <= new_euros;
      } 
      // BUG FIX: de [>= y <= a > y <]
      // Si tenemos valores en cero no deberia ni quitar ni poner montos a ninguna variable
      if (new_cents > 0 && new_euros < 0) {
        new_cents = new_cents - 100; 
        new_euros = new_euros + 1;
        //@ assert new_cents >= -100;
        //@ assert Integer.MAX_VALUE >= new_euros;
      }
      return new Amount(new_euros, new_cents);
    }
   
    /*@ requires a != null;
      @ requires this.euros == a.euros;
      @ requires this.cents == a.cents;
      @ ensures \result == true || \result == false;
      @*/
    public boolean equal(/*@ non_null @*/ Amount a) {
      //@ assert Integer.MIN_VALUE <= this.euros <= Integer.MAX_VALUE;
      //@ assert Integer.MIN_VALUE <= this.cents <= Integer.MAX_VALUE;
      if (a==null) return false;
      else return (euros == a.euros && cents == a.cents);
    }
}
   