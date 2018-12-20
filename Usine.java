/*@predicate tache(Tache tache; int temps_necessaire, int gain) =
	tache.temps_necessaire |-> temps_necessaire &*&
	tache.gain |-> gain &*&
	temps_necessaire >= 0 &*& gain >= 0;
@*/
class Tache {
	private int temps_necessaire;
	private int gain;
	
	public Tache(int temps_necessaire, int gain)
	//@requires temps_necessaire >= 0 && gain >= 0;
	//@ensures tache(this, temps_necessaire, gain);
	{
		this.temps_necessaire = temps_necessaire;
		this.gain = gain;
	}
	
	public int get_temps_necessaire()
	//@requires tache(this, ?tn, ?gain);
	//@ensures tache(this, tn, gain) &*& result == tn;
	{
		return this.temps_necessaire;
	}
	
	public int get_gain()
	//@requires tache(this, ?tn, ?g);
	//@ensures tache(this, tn, g) &*& result == g;
	{
		return this.gain;
	}
}

/*@predicate travailleur(Travailleur travailleur; int temps_dispo, int salaire_horaire, int salaire_percu) = 
	travailleur.temps_dispo |-> temps_dispo &*&
	travailleur.salaire_horaire |-> salaire_horaire &*&
	travailleur.salaire_percu |-> salaire_percu &*& temps_dispo>=0;
@*/
class Travailleur {
	private int temps_dispo;
	private int salaire_horaire;
	private int salaire_percu;
	
	//private int temps_travail; //TODO : question 6
	
	public Travailleur(int temps_dispo, int salaire_horaire)
	//@requires salaire_horaire >= 0 && temps_dispo>=0;
	//@ensures travailleur(this, temps_dispo, salaire_horaire, 0);
	{
		this.temps_dispo = temps_dispo;
		this.salaire_horaire = salaire_horaire;
		this.salaire_percu = 0;
	}
	
	public int get_temps_dispo()
	//@requires travailleur(this, ?td, ?sh, ?sp);
	//@ensures travailleur(this, td, sh, sp) &*& result == td;
	{
		return this.temps_dispo;
	}
	
	public int get_salaire_horaire()
	//@requires travailleur(this, ?td, ?sh, ?sp);
	//@ensures travailleur(this, td, sh, sp) &*& result == sh;
	{
		return this.salaire_horaire;
	}
	
	public int get_salaire_percu()
	//@requires travailleur(this, ?td, ?sh, ?sp);
	//@ensures travailleur(this, td, sh, sp) &*& result == sp;
	{
		return this.salaire_percu;
	}
	
	public int travailler(int t)
	//@requires travailleur(this, ?td, ?sh, ?sp) &*& t >= 0;
	/*@ensures td >= t ? travailleur(this, td-t, sh, sp+result) &*& result == sh*t
			   : travailleur(this,td,sh,sp+result) &*& result == 0;
	@*/
	{
		int salaire = 0;
		if (this.temps_dispo >= t) {
			this.temps_dispo = this.temps_dispo - t;
			salaire = this.salaire_horaire * t;
			this.salaire_percu = this.salaire_percu + salaire;
		}
		return salaire;
	}
}



/*@predicate usine(Usine usine; int balance) = usine.balance |-> balance;
@*/
class Usine {
    private int balance;
    
    public Usine(int depot_initial)
    //@requires true;
    //@ensures usine(this, depot_initial);
    {
        this.balance = depot_initial;
    }
    
    public int get_balance()
    //@requires usine(this, ?b);
    //@ensures usine(this, b) &*& result == b;
    {
        return this.balance;
    }
    
    public void depose_argent(int argent)
    //@requires usine(this, ?b);
    //@ensures usine(this, b+argent);
    {
        this.balance = this.balance + argent;
    }
    
    public void effectueTache(Tache tache, Travailleur travailleur)
    /*@requires usine(this, ?b) &*& tache(tache, ?tn, ?g) &*& travailleur(travailleur, ?td, ?sh, ?sp);
    @*/
    /*@ensures ((td>=tn) && (g-tn*sh>0)) ? (usine(this, b+g-tn*sh) &*& travailleur(travailleur, td-tn, sh, sp+tn*sh))
			: (usine(this, b) &*& travailleur(travailleur,td,sh,sp) &*& tache(tache,tn,g));
    @*/
    {   
    	//@open tache(tache, tn, g);
    	//@open travailleur(travailleur, td, sh, sp); 
        int temps_dispo = travailleur.get_temps_dispo();
        int temps_nece = tache.get_temps_necessaire();
        
        //Si il reste suffisamment de temps disponible pour que le travailleur travaille sur sa tache
        if(temps_dispo-temps_nece >=0 && est_rentable(tache,travailleur))
        {
            int benefice = tache.get_gain();
            int perte = travailleur.travailler(temps_nece);
            depose_argent(benefice-perte);            
        }
    }

    public static boolean est_rentable(Tache tache, Travailleur travailleur)
    //@requires tache(tache, ?tn, ?g) &*& travailleur(travailleur, ?td, ?sh, ?sp);
    /*@ensures result == (g-tn*sh>0) &*& tache(tache,tn,g) &*& travailleur(travailleur,td,sh,sp);
    @*/
    {
    	//@open tache(tache, _, _);
    	//@open travailleur(travailleur, _, _, _);
    	int temps_nece = tache.get_temps_necessaire();
    	int gain = tache.get_gain();
    	int cout_salarial = travailleur.get_salaire_horaire() * temps_nece;
    	return (gain - cout_salarial > 0);
    }
    
}


class UsineTest {

	public static void main(String[] args)
	//@requires true;
	//@ensures true;
	{
		//Test de tache
		Tache tache = new Tache(2,50);
		
		int temps_necessaire = tache.get_temps_necessaire();
		assert temps_necessaire == 2;
		
		int gain = tache.get_gain();
		assert gain == 50;
		
		//Test de travailleur
		Travailleur travailleur  = new Travailleur(35,15);
		
		int temps_dispo = travailleur.get_temps_dispo();
		assert temps_dispo == 35;
		
		int salaire_horaire = travailleur.get_salaire_horaire();
		assert salaire_horaire == 15;
		
		int salaire_percu = travailleur.get_salaire_percu();
		assert salaire_percu == 0;
		
		int travail = travailleur.travailler(10);
		assert travail == 150;
		
		salaire_percu = travailleur.get_salaire_percu();
		assert salaire_percu == 150;
		
		temps_dispo = travailleur.get_temps_dispo();
		assert temps_dispo == 25;
		
		//Test de usine
		Usine usine = new Usine(50);
		
		int balance = usine.get_balance();
		assert balance == 50;
		
		int depot = 10;
		usine.depose_argent(depot);
		
		balance = usine.get_balance();
		assert balance == 60;
				
		usine.effectueTache(tache, travailleur);
		
		temps_dispo = travailleur.get_temps_dispo();
		assert temps_dispo == 23;
		
		salaire_percu = travailleur.get_salaire_percu();
		assert salaire_percu == 180;
		
		balance = usine.get_balance();
		assert balance == 80;
		
	//	boolean rentabilite = usine.est_rentable(tache,travailleur);
	//	assert rentabilite == true;
		
		//TEST BIS
		/*Travailleur idiot = new Travailleur(-35,15);
		int temps_dispo = travailleur.get_temps_dispo();
		assert temps_dispo == -35;
		*/
		
	}
}