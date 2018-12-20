//@predicate estEmbauche(Usine usine, Travailleur travailleur) = true;
//@predicate peutEtreEffectuee(Tache tache) = true;




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
	//@ensures tache(this, temps_necessaire, gain) &*& peutEtreEffectuee(this);
	{
		this.temps_necessaire = temps_necessaire;
		this.gain = gain;
		//@close peutEtreEffectuee(this);
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



/*@predicate usine(Usine usine; int depense_salaire, int gain_accumule) = usine.depense_salaire |-> depense_salaire &*& usine.gain_accumule |-> gain_accumule;
@*/
class Usine {
    private int depense_salaire;
    private int gain_accumule;
    
    public Usine(int depense_salaire, int gain_accumule)
    //@requires true;
    //@ensures usine(this, depense_salaire, gain_accumule);
    {
        this.depense_salaire = depense_salaire;
        this.gain_accumule = gain_accumule;
    }
    
    public Usine()
    //@requires true;
    //@ensures usine(this, 0, 0);
    {
        this.depense_salaire = 0;
        this.gain_accumule = 0;
    }
    
    public int get_depense_salaire()
    //@requires usine(this, ?ds, ?ga);
    //@ensures usine(this, ds, ga) &*& result == ds;
    {
        return this.depense_salaire;
    }
    
    public int get_gain_accumule()
    //@requires usine(this, ?ds, ?ga);
    //@ensures usine(this, ds, ga) &*& result == ga;
    {
        return this.gain_accumule;
    }

	public int get_balance()
	//@requires usine(this, ?ds, ?ga);
    	//@ensures usine(this, ds, ga) &*& result == ga-ds;
	{
		return (this.gain_accumule - this.depense_salaire);
	}
	
	
    public void payer_employer(int montant)
    //@requires usine(this, ?ds, ?ga);
    //@ensures usine(this, ds+montant, ga);
    {
	this.depense_salaire = this.depense_salaire + montant;
    }
    
    public void recette(int montant)
    //@requires usine(this, ?ds, ?ga);
    //@ensures usine(this, ds, ga+montant);
    {
	this.gain_accumule = this.gain_accumule + montant;
    }  
  
    public static boolean est_rentable(Tache tache, Travailleur travailleur)
    //@requires tache(tache, ?tn, ?g) &*& travailleur(travailleur, ?td, ?sh, ?sp);
    //@ensures result == (g-tn*sh>0) &*& tache(tache,tn,g) &*& travailleur(travailleur,td,sh,sp);
    {
    	//@open tache(tache, _, _);
    	//@open travailleur(travailleur, _, _, _);
    	int temps_nece = tache.get_temps_necessaire();
    	int gain = tache.get_gain();
    	int cout_salarial = travailleur.get_salaire_horaire() * temps_nece;
    	return (gain - cout_salarial > 0);
    }    
    
    public void effectueTache(Tache tache, Travailleur travailleur)
    /*@requires usine(this, ?ds, ?ga) &*&
    		tache(tache, ?tn, ?g) &*&
    		travailleur(travailleur, ?td, ?sh, ?sp) &*&
    		estEmbauche(this, travailleur) &*&
    		peutEtreEffectuee(tache) &*&
    		td > 0; @*/
    /*@ensures ((td>=tn) && (g-tn*sh>0)) ? usine(this, ds+tn*sh, ga+g) &*&
    						travailleur(travailleur, td-tn, sh, sp+tn*sh) &*&
    						tache(tache,tn,g) &*&
    						estEmbauche(this, travailleur)
					 : usine(this, ds, ga) &*&
					 	travailleur(travailleur,td,sh,sp) &*&
					 	tache(tache,tn,g) &*&
					 	estEmbauche(this, travailleur) &*&
					 	peutEtreEffectuee(tache);@*/
    {   
    	//@open tache(tache, tn, g);
    	//@open travailleur(travailleur, td, sh, sp); 
        int temps_dispo = travailleur.get_temps_dispo();
        int temps_nece = tache.get_temps_necessaire();
        
        //Si il reste suffisamment de temps disponible pour que le travailleur travaille sur sa tache
        if(temps_dispo-temps_nece >=0 && est_rentable(tache,travailleur))
        {
            recette(tache.get_gain());
            payer_employer(travailleur.travailler(temps_nece));
            //@open peutEtreEffectuee(tache);
        }

    }
   
    
    
    
	public void embaucher(Travailleur travailleur)
	/*@requires travailleur(travailleur, ?temps_dispo, ?salaire_horaire, ?salaire_percu); @*/
	/*@ensures travailleur(travailleur, temps_dispo, salaire_horaire, salaire_percu) &*& estEmbauche(this,travailleur); @*/
	{
		//@close estEmbauche(this, travailleur);
	}
	
	public void licencier(Travailleur travailleur)
	/*@requires travailleur(travailleur, ?temps_dispo, ?salaire_horaire, ?salaire_percu) &*& estEmbauche(this,travailleur); @*/
	/*@ensures travailleur(travailleur, temps_dispo, salaire_horaire, salaire_percu); @*/
	{
		//@open estEmbauche(this, travailleur);
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
		Usine usine = new Usine();
		
		int depense_salaire = usine.get_depense_salaire();
		assert depense_salaire == 0;
		
		int gain_accumule = usine.get_gain_accumule();
		assert gain_accumule == 0;
		
		usine.recette(100);
		gain_accumule = usine.get_gain_accumule();
		assert gain_accumule == 100;
		
		usine.payer_employer(100);
		depense_salaire = usine.get_depense_salaire();
		assert depense_salaire == 100;
		
		int balance = usine.get_balance();
		assert balance == 0;
		
		usine.embaucher(travailleur);
		usine.effectueTache(tache, travailleur);
		
		temps_dispo = travailleur.get_temps_dispo();
		assert temps_dispo == 23;
		
		salaire_percu = travailleur.get_salaire_percu();
		assert salaire_percu == 180;

		gain_accumule = usine.get_gain_accumule();
		assert gain_accumule == 150;

		depense_salaire = usine.get_depense_salaire();
		assert depense_salaire == 130;
		
		
		//TESTS QUESTION 14 ET 15
		Tache film = new Tache(10,1000);
		Travailleur walt = new Travailleur(35,10);
		Usine disney = new Usine();
		disney.embaucher(walt);
		disney.effectueTache(film, walt); //EffectueTache ne marche bien pas si l'on ne met en disney.embaucher(walt)
		//disney.effectueTache(film, walt); //Si on retente d'effectuer la tâche film, on a bien aucune correspondance pour le prédicat peutEtreEffectuee(film)
		
		//Test question 16
		Tache film_animation = new Tache(10,900);
		//disney.licencier(walt);
		disney.effectueTache(film_animation, walt); //Si l'on licencie walt (ligne commentée en haut), l'on a bien aucune correspondance pour le prédicat estEmbauche(disney,walt)
		
		//Test question 17
		Tache film_blockBuster = new Tache(10, 5000);
		Travailleur michel_baie = new Travailleur(0,20);
		disney.embaucher(michel_baie);
		//disney.effectueTache(film_blockBuster, michel_baie); //Comme prévue, cette tâche ne peut pas être effectuée car michelBaie car il a 0 en temps_dispo
		
	}
}
