public class testAmount{

    //@ spec_public
    private int cents;    
    //@ spec_public
    private int euros;
    
    /*@ ensures this.euros == euros && this.cents == cents;
      @*/
    public testAmount(int euros, int cents){
      this.euros = euros;
      this.cents = cents;
    }
       
    /*@ requires a != null;
      @ requires Integer.MIN_VALUE < (this.euros + a.euros) < Integer.MAX_VALUE;
      @ requires Integer.MIN_VALUE < (this.cents + a.cents) < Integer.MAX_VALUE;
      @ ensures \result != null;
      @*/
    public testAmount add(/*@non_null@*/testAmount a){
      int new_euros = euros + a.euros; 
      //@ assert Integer.MIN_VALUE < (new_euros) < Integer.MAX_VALUE;
      int new_cents = cents + a.cents; 
      //@ assert Integer.MIN_VALUE < (new_cents) < Integer.MAX_VALUE;
      if (new_cents <= -100) {  
        new_cents = new_cents + 100;
        //@ assert Integer.MIN_VALUE < (new_cents) < Integer.MAX_VALUE;
        new_euros = new_euros - 1;
      } 
      if (new_cents >= 100) {  
        new_cents = new_cents - 100;
        new_euros = new_euros + 1;
      } 
      if (new_cents < 0 && new_euros > 0) { 
        new_cents = new_cents + 100; 
        new_euros = new_euros - 1;
      } 
      if (new_cents > 0 && new_euros < 0) {
        new_cents = new_cents - 100; 
        new_euros = new_euros + 1;
      }
      return new testAmount(new_euros, new_cents);
     }
   
   }
   