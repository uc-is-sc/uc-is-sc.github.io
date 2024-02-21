theory perfUCisRC
  imports
    HOL.Real
    HOL.Option
    "HOL-Library.Monad_Syntax"
begin

section "Requirements for UC-style compositionality"

datatype ('color) prgm = Prgrm 'color
datatype ('color) ctxt = Ctxt 'color
datatype ('color) whle = Whle 'color

partial_function (tailrec) oddity :: "nat => nat"
where "oddity arg = (case arg of (Suc (Suc n)) => n | 0 => 0 )"

consts 
  call:: "'blue prgm \<Rightarrow> 'red prgm \<Rightarrow> 'blue prgm" (infixr "\<circ>\<circ>"  60)
  bigcall:: "'blue whle \<Rightarrow> 'red whle \<Rightarrow> 'blue whle" (infixr "\<circ>\<circ>\<circ>" 52)
  par:: "'blue ctxt \<Rightarrow> 'red ctxt \<Rightarrow> 'blue ctxt" (infixl "\<parallel>" 60)
  link:: "'b ctxt \<Rightarrow> 'b prgm \<Rightarrow> 'b whle" (infixl "><" 55) 
  ple :: "'c whle \<Rightarrow> 'd whle \<Rightarrow> bool" (infixl "\<lesssim>" 50)

abbreviation RRgen:: "('r whle \<Rightarrow> 'b whle \<Rightarrow> bool) \<Rightarrow> 'r prgm \<Rightarrow> 'b prgm \<Rightarrow> bool" 
  where
  "RRgen rel (p::'r prgm) (f::'b prgm) \<equiv> 
    \<forall> (A::'r ctxt). \<exists> (S::'b ctxt). rel (A >< p) (S >< f)"

abbreviation RR:: "'r prgm \<Rightarrow> 'b prgm \<Rightarrow> bool" ("_ robustly-refines _" [20,20] 17)
  where
  "RR p f \<equiv> RRgen ple p f"


locale composition =
  assumes par_decomp: (* parallel decomposition (for pink programs using red programs) *)
  "\<forall> (A::'p ctxt) (P1::'p prgm) (P2::'r prgm) .
             \<exists> (A1::'p ctxt) (A2::'r ctxt).
      A >< P1 \<circ>\<circ> P2 \<lesssim> A1 \<parallel> A2 >< P1 \<circ>\<circ> P2"
  and inter_comp: (* intertwined composition (dito) *)
  "\<forall> (P1::'p prgm) (P2::'r prgm) 
              (A1::'p ctxt) (A2::'r ctxt).
       A1 \<parallel> A2 >< P1 \<circ>\<circ> P2 \<lesssim> A1 >< P1 \<circ>\<circ>\<circ> A2 >< P2"
  and inter_decomp: (* intertwined composition (for pink programs using blue programs) *)
  "\<forall> (P1::'p prgm) (P2::'b prgm) A1 A2 .
    A1 >< P1 \<circ>\<circ>\<circ> A2 >< P2  \<lesssim>   A1 \<parallel> A2 >< P1 \<circ>\<circ> P2 "
  and  const_elim: (* constant elimination (for plugging substituting red with blue in pink contexts*)
  "\<forall> (redW::'r whle) (blueW::'b whle) (pinkW::'p whle) .
       ( (redW \<lesssim> blueW) \<longrightarrow> ( pinkW \<circ>\<circ>\<circ> redW \<lesssim> pinkW \<circ>\<circ>\<circ> blueW))"
  and transitivity [simp,trans]: (* transitivity of trace relation for pink programs *)
  "(W1::'p whle) \<lesssim> (W2::'p whle)
    \<Longrightarrow>  W2 \<lesssim> (W3::'p whle)  \<Longrightarrow> W1 \<lesssim> W3"

(* new axioms for dummy adversary theorem *)
locale dummy =
 (* dummy context and program *)
 fixes Pd::"'r prgm" (* Z\<rightarrow>Pd \<Rightarrow> Z\<rightarrow>Psub, A\<rightarrow>Pd\<Rightarrow> undefined  , Psub\<rightarrow>Pd\<Rightarrow> Psub\<Rightarrow>Z, *)
 fixes Ad::"'r ctxt" (* Z\<rightarrow>Ad \<Rightarrow> Z\<rightarrow>P,    P\<rightarrow> Ad \<Rightarrow> P\<rightarrow>Z *)
 assumes adv_split:
 "\<forall> A (P::'r prgm) . \<exists> A' . A >< Pd\<circ>\<circ>P \<lesssim> (A' \<parallel> Ad) >< Pd\<circ>\<circ>P" 
 and prog_unsplit: 
 "\<forall>(A::'r ctxt) (P::'b prgm) . \<exists> (A'::'b ctxt) . A >< (Pd \<circ>\<circ> P) \<lesssim> A' >< P"  
 and prog_split:
 "\<forall>(A::'r ctxt) (P::'r prgm) . \<exists> (A'::'r ctxt) . A >< P \<lesssim>  A' >< (Pd \<circ>\<circ> P)"  
 and  const_elim2: (* constant elimination for red contexts *)
 "\<forall>(redW::'r whle) (blueW::'b whle) (W::'r whle) .
       ( (redW \<lesssim> blueW) \<longrightarrow> ( W \<circ>\<circ>\<circ> redW \<lesssim> W \<circ>\<circ>\<circ> blueW))"
 and inter_comp2: (* intertwined composition (for red  programs) *)
 "\<forall>(P1::'r prgm) (P2::'r prgm) 
              (A1::'r ctxt) (A2::'r ctxt).
       A1 \<parallel> A2 >< P1 \<circ>\<circ> P2 \<lesssim> A1 >< P1 \<circ>\<circ>\<circ> A2 >< P2"
 and inter_decomp2: (* intertwined composition (for pink programs using blue programs) *)
 "\<forall> (P1::'r prgm) (P2::'b prgm) A1 A2.
    A1 >< P1 \<circ>\<circ>\<circ> A2 >< P2  \<lesssim>  A1 \<parallel> A2 >< P1 \<circ>\<circ> P2 "
 and transitivity2 [trans]: (* transitivity of trace relation for red programs *)
 "\<lbrakk>(W1::'r whle) \<lesssim> (W2::'r whle); W2 \<lesssim> (W3::'r whle)\<rbrakk> \<Longrightarrow> W1 \<lesssim> W3"
 and transitivity3 [trans]: (* transitivity of trace relation from red-to-red to red-to-blue  *)
 "\<lbrakk>(W1'::'r whle) \<lesssim> (W2'::'r whle); W2' \<lesssim> (W3'::'b whle)\<rbrakk> \<Longrightarrow> W1' \<lesssim> W3'" 
context dummy
begin

theorem dummy:
  fixes P::"'r prgm"
  fixes F::"'b prgm"
  assumes A: " \<exists> (S::'b ctxt) . Ad >< P \<lesssim> S >< F"
shows "\<forall> (A::'r ctxt). \<exists> (S::'b ctxt) . A >< P \<lesssim> S >< F"
proof
  fix A 
  from prog_split obtain A' where "A >< P \<lesssim> A' >< (Pd \<circ>\<circ> P)" by auto
  also obtain  A'' where "... \<lesssim> A'' \<parallel> Ad >< Pd \<circ>\<circ> P" using adv_split by auto 
  also have "... \<lesssim> (A'' >< Pd) \<circ>\<circ>\<circ> (Ad >< P)" using inter_comp2 by blast
  also obtain S where "... \<lesssim> (A'' >< Pd) \<circ>\<circ>\<circ> (S >< F)" using A const_elim2 by blast
  also have "... \<lesssim> ((A'' \<parallel> S) >< (Pd \<circ>\<circ> F))" using inter_decomp2 by blast
  also obtain S' where "... \<lesssim> S' >< F" using prog_unsplit by blast
  finally have Almost:"A >< P \<lesssim> S' >< F".
  thus "\<exists> (S::'b ctxt) . A >< P \<lesssim> S >< F" by auto
 qed
end

context composition
begin

theorem composition:
  fixes P::"'r prgm"
  fixes F::"'b prgm"
  fixes R::"'p prgm"
  assumes A: "P robustly-refines F"
  shows "R \<circ>\<circ> P robustly-refines R \<circ>\<circ> F"
proof
  fix A
  from par_decomp obtain A1 A2 where "(A >< R \<circ>\<circ> P) \<lesssim> ((A1::'p ctxt) \<parallel> (A2:: 'r ctxt) >< R \<circ>\<circ> P)" by presburger
  also have  "... \<lesssim>  (A1 >< R \<circ>\<circ>\<circ> A2 >< P)" by (simp add:inter_comp)
  finally have OK:"(A >< R \<circ>\<circ> P) \<lesssim>  (A1 >< R \<circ>\<circ>\<circ> A2 >< P)".
  
  from A obtain S2 where "(A2 >< P) \<lesssim> (S2 >< F)" by auto
  hence "(A1 >< R) \<circ>\<circ>\<circ> (A2 >< P) \<lesssim> (A1 >< R) \<circ>\<circ>\<circ> (S2 >< F)" by (simp add:const_elim)
  also have "... \<lesssim> (A1 \<parallel> S2) >< (R \<circ>\<circ> F)" by (simp add:inter_decomp)
  finally have  "(A1 >< R) \<circ>\<circ>\<circ> (A2 >< P) \<lesssim> (A1 \<parallel> S2) >< (R \<circ>\<circ> F)".
  from this OK have "(A >< R \<circ>\<circ> P) \<lesssim> (A1 \<parallel> S2) >< (R \<circ>\<circ> F)" by (meson transitivity)   
  then show "\<exists> S . (A >< R \<circ>\<circ> P) \<lesssim> S >< (R \<circ>\<circ> F)" by metis
qed

end

section "Relating UC to RSCP"

type_synonym ('b,'r) comp = "'b prgm \<Rightarrow> ('r prgm) option"

consts
       leadsto :: "'a whle \<Rightarrow> 't \<Rightarrow> bool" (infixr "\<leadsto>" 51)
       prefix :: "'t \<Rightarrow> bool"

(* We instantiate RSCHP from RRgen above for modularity. *)
abbreviation RSCHPrel
  where
  "RSCHPrel (t:: 't itself) W W' \<equiv> (\<forall> m :: 't . prefix m \<longrightarrow>  W \<leadsto> m \<longrightarrow>  W' \<leadsto> m)"


abbreviation RSCHP
  where
  "RSCHP C (t:: 't itself) \<equiv> \<forall> P. (case C P of 
              Some CP \<Rightarrow>  RRgen (RSCHPrel (t:: 't itself)) (CP) P
              | None \<Rightarrow> True 
            )"


locale UC = 
  fixes PrExec  :: "'env \<Rightarrow> 'uc ctxt \<Rightarrow> 'uc prgm \<Rightarrow> bool \<Rightarrow> real"
  fixes PrExecT :: "'env \<Rightarrow> 'uc ctxt \<Rightarrow> 'uc prgm \<Rightarrow> 't \<Rightarrow> real"
    (* Note: PrExec and PrExecT are total function. Hence, when the random vars Exec or ExecT are
       undefined, we give them probability zero.  *)
  fixes \<beta> :: "'t \<Rightarrow> bool" (* extracts final bit from trace *) 
  fixes Zcan :: "'t \<Rightarrow> 'env" (* canonical Z: produces messages to A and P as specified by t *)
  fixes nonprobabilistic :: "'env \<Rightarrow> bool"
  
  (* assumptions needed in both directions *)
  assumes relation_uc: (* We can define a semantic's from UC's semantics. *)
    "prefix t \<longrightarrow>  (A >< P) \<leadsto> (t,p) \<equiv> (PrExecT (Zcan t) A P t) = p \<and> p > 0"
  and prefix_iff_trace_is_prefix: (* PL-level trace (i.e., tuple) is prefix is the UC trace in it is. *)
    "prefix (t::'t,p::real) \<equiv> prefix t"

  (* only needed in RSCHPtoUC *)
  and prefixes_contain_final_bit: (* every finite trace contains the final bit *)
    "PrExec Z A P b = (\<Sum> t \<in> {t. prefix t \<and> \<beta> t = b}  . PrExecT Z A P t)"
  and nonprobabilistic_envs_are_complete:
    "(\<exists> Z b. PrExec Z A P b \<noteq> PrExec Z S F b) \<longrightarrow> (\<exists> Z' . PrExec Z' A P True \<noteq> PrExec Z' S F True \<and> nonprobabilistic Z')"  
  and construct_canonical_env:
    "\<lbrakk>nonprobabilistic Z;  prefix t; (\<exists> A' P' . PrExecT Z A' P' t > 0) \<rbrakk> \<Longrightarrow> PrExecT Z A P t = PrExecT (Zcan t) A P t"

  (* only needed in UCtoRSCHP *)
  and construct_canonical_env2:
    "\<lbrakk>prefix t \<rbrakk> \<Longrightarrow> PrExecT (Zcan t) A P t = PrExec (Zcan t) A P True"

  (* axioms of probabilities *)
  and unit_interval: "PrExec Z A P True = 1- PrExec Z A P False"
  and unit_interval_min: "PrExec Z A P b \<ge> 0"
  and PrExecT_unit_interval_min: "PrExecT Z A P t \<ge> 0"

context UC
begin

abbreviation UCemulates:: "'uc prgm \<Rightarrow> 'uc prgm \<Rightarrow> bool" (infixl "UC-emulates" 45)
  where
  "UCemulates P F \<equiv> \<forall> A . \<exists> (S::'uc ctxt) . \<forall> (Z::'env). 
    (PrExec Z A P True = PrExec Z S F True)"

lemma UCemulates_reflexive:
  fixes P::"'uc prgm"
  shows "P UC-emulates P"
  by metis

lemma difference_in_sum' :
  fixes f:: "'a \<Rightarrow> real"
  fixes g:: "'a \<Rightarrow> real"
  assumes A:" (\<Sum> x\<in> P . f x) > (\<Sum>x \<in> P . g x)"
  shows "\<exists> x\<in>P . f x > g x "
proof (rule ccontr)
  assume CF: "\<not>(\<exists> x\<in>P . f x > g x)"
  then show "False" 
  proof -
    from CF have "\<forall> x\<in> P.  f x \<le>  g x" by auto
    hence "\<forall>x.  (x\<in>P \<longrightarrow> f x \<le> g x)" by simp
    from this sum_mono have "(\<Sum>x\<in>P. f x) \<le> (\<Sum>x\<in>P. g x)" by metis
    thus "False" using A by arith 
  qed
qed

lemma distinguishingZ_differentTrace:
  assumes A: "PrExecT Z A P t \<noteq> PrExecT Z S F t"
  and  B: "PrExecT Z A P t > 0"
  and Z : "nonprobabilistic Z"
  and T : "prefix t"
  shows "\<exists> p ::real .(A >< P) \<leadsto> (t,p) \<and> \<not>((S >< F) \<leadsto> (t,p))"
proof -
  from B have t_possible_in_Z: "\<exists> A' P' . PrExecT Z A' P' t > 0" by auto
  from Z construct_canonical_env A T t_possible_in_Z have A':"PrExecT (Zcan t) A P t \<noteq> PrExecT (Zcan t) S F t" by fastforce
  from Z construct_canonical_env B T have B': "PrExecT (Zcan t) A P t > 0" by fastforce

  let ?p = "PrExecT (Zcan t) A P t"
  from relation_uc B' have Yes: "(A >< P) \<leadsto> (t,?p)" by blast
  have No: "\<not>((S >< F) \<leadsto> (t,?p))"
  proof (rule ccontr)
    assume C:"\<not>\<not>(S >< F) \<leadsto> (t,?p)"
    show "False"
    proof -
      from C relation_uc T have "(PrExecT (Zcan t) S F t) = ?p \<and> ?p > 0" by metis
      hence "PrExecT (Zcan t) S F t = ?p" by auto
      from this A' show "False" by simp
    qed
  qed
  from Yes No show ?thesis by auto
qed

lemma greater_to_unequal_and_nonzero:
  assumes Greater: "PrExecT Z A P t > PrExecT Z S F t"
  shows "PrExecT Z A P t \<noteq> PrExecT Z S F t \<and> PrExecT Z A P t > 0"
proof -
  from PrExecT_unit_interval_min have "PrExecT Z S F t \<ge>  0" by simp
  from this Greater have B:"PrExecT Z A P t > 0" by fastforce 
  from this Greater show ?thesis by auto
qed

lemma PrExec_bit_selects_inequality:
  assumes "PrExec Z A P True \<noteq> PrExec Z' A' P' True"
  shows "\<exists> b. PrExec Z A P b > PrExec Z' A' P' b"
proof -
  consider 
        (A) "PrExec Z A P True > PrExec Z' A' P' True" 
      | (B) "PrExec Z A P True < PrExec Z' A' P' True"
     using assms by fastforce 
  then show ?thesis 
  proof cases
    case A then show ?thesis by auto
  next
    case B then show ?thesis using unit_interval by auto
  qed
qed

theorem RSCHPtoUC':
  fixes C ::"('uc,'uc) comp"
  fixes ttype :: "('t \<times> real) itself"
  fixes P::"'uc prgm"
  fixes CP::"'uc prgm"
  assumes CP: "C P = Some CP"
  assumes A: "\<forall> A:: 'uc ctxt . \<exists> S::'uc ctxt.
                 \<forall> (m:: ('t \<times> real)). prefix m \<longrightarrow>  A >< CP \<leadsto> m \<longrightarrow> S >< P \<leadsto> m"
  shows " CP UC-emulates P"
proof (rule ccontr)
  assume CF: "\<not> CP UC-emulates P"
  then show "False" 
  proof -
     from CF obtain A::"'uc ctxt" where CF1:"\<forall> (S::'uc ctxt) . \<exists> (Z::'env).
       PrExec Z A (CP) True \<noteq> PrExec Z S P True" by auto

    from A obtain S::"'uc ctxt" where
      A1: "\<forall> (m:: ('t \<times> real)). prefix m \<longrightarrow>  A >< CP \<leadsto> m \<longrightarrow> S >< P \<leadsto> m" by blast

    from CF1 have "\<exists> Z . PrExec Z A CP True \<noteq> PrExec Z S P True"
      by auto
    hence 
       "\<exists> Z . PrExec Z A CP True \<noteq> PrExec Z S P True \<and> nonprobabilistic Z" 
      using nonprobabilistic_envs_are_complete by metis
    then obtain Z::"'env" 
      where "PrExec Z A (CP) True \<noteq> PrExec Z S P True"
      and Prob: "nonprobabilistic Z"
      by auto

    (* Need to select a bit here so that one is larger than the other.*)
    then obtain b::"bool" where "PrExec Z A (CP) b > PrExec Z S P b"
        using PrExec_bit_selects_inequality by metis
      hence "(\<Sum> t\<in> {t. prefix t \<and> \<beta> t= b} . 
        PrExecT Z A (CP) t) > (\<Sum> t\<in>{t . prefix t \<and> \<beta> t = b} . PrExecT Z S P t)" 
      using prefixes_contain_final_bit by simp
    then obtain t::"'t" 
        where "PrExecT Z A (CP) t > PrExecT Z S P t"
        and Prefix: "prefix t" using difference_in_sum' by fastforce
    then have "PrExecT Z A (CP) t \<noteq> PrExecT Z S P t"
         and  "PrExecT Z A (CP) t > 0"
         using greater_to_unequal_and_nonzero by auto
    then obtain p::"real" where "A >< (CP) \<leadsto> (t,p) \<and> \<not>((S >< P) \<leadsto> (t,p)) "
         using Prob Prefix distinguishingZ_differentTrace by metis
    moreover have "prefix (t,p)" using Prefix prefix_iff_trace_is_prefix by auto
    ultimately show False using A1 by fastforce
qed 
qed


theorem RSCHPtoUC:
  fixes C ::"('uc,'uc) comp"
  fixes ttype :: "('t \<times> real) itself"
  assumes A: "RSCHP C ttype"
  shows "\<forall> (P::'uc prgm) . case C P of Some CP \<Rightarrow> CP UC-emulates P | None \<Rightarrow> True"
proof
  fix P
  show "case C P of Some CP \<Rightarrow> CP UC-emulates P | None \<Rightarrow> True"
  proof (cases "C P")
    case None
    then show ?thesis by simp
  next
    case A1: (Some CP)
    hence A2:"
         \<forall>A. \<exists>S. \<forall>m. prefix (m::('t \<times> real)) \<longrightarrow>
                           A >< CP \<leadsto> m \<longrightarrow> S >< P \<leadsto> m
         " by (smt (verit, best) A1 assms option.simps(5))  
    then show ?thesis using RSCHPtoUC' A1 A2 by simp 
  qed
qed

theorem UCtoRSCHP:
  fixes C ::"('uc,'uc) comp"
  fixes ttype :: "('t \<times> real) itself"
  assumes A1: "\<forall> (P::'uc prgm) . case C P of Some CP \<Rightarrow> CP UC-emulates P | None \<Rightarrow> True"
  shows "RSCHP C ttype"
proof (rule ccontr)
  assume CF: "\<not> (RSCHP C ttype)"
  then show "False" 
  proof -
    from CF obtain P  where  CF':"
          \<not>( case C P of None \<Rightarrow> True
          | Some CP \<Rightarrow>
              \<forall>A. \<exists>S. \<forall>m :: ('t \<times> real). prefix m \<longrightarrow>
                          A >< CP \<leadsto> m \<longrightarrow> S >< P \<leadsto> m)" by auto
    hence "\<exists> CP . C P = Some CP"   using option.simps(4) by fastforce
    then obtain CP where SomeCP: "C P  = Some (CP::'uc prgm)" by auto
    from CF' SomeCP have "\<not>(\<forall>A. \<exists>S. \<forall>m :: ('t \<times> real). prefix m \<longrightarrow>
                          A >< CP \<leadsto> m \<longrightarrow> S >< P \<leadsto> m)" by auto
    then obtain A where  NotRSCHP: "\<forall> (S::'uc ctxt).
      (\<exists> m :: ('t \<times> real) . prefix m \<and> (A >< (CP::'uc prgm) \<leadsto> m) \<and> \<not>(S >< P \<leadsto> m))" by auto
    from A1 SomeCP have "CP UC-emulates P "  by (smt (verit, del_insts) option.simps(5)) 
    then obtain S where Eq: "\<forall> (Z::'env) . (PrExec Z A (CP) True = PrExec Z S P True)" by blast
    from NotRSCHP have
      "(\<exists>  (t::'t) (p::real) . prefix (t,p) \<and> (A >< (CP) \<leadsto> (t,p)) \<and> \<not>(S >< P \<leadsto> (t,p)))"
      by auto 
    then obtain  t :: "'t" and p :: "real"
      where prefix_full: "prefix (t,p)" 
      and Yes:"A >< (CP) \<leadsto> (t,p)"
      and No: "\<not>(S >< P \<leadsto> (t,p))" by auto
    from prefix_full prefix_iff_trace_is_prefix have prefix: "prefix t" by simp

    let ?Z = "Zcan t"
    from Yes relation_uc prefix have PrEx1: "PrExecT ?Z A (CP) t = p" by metis
    from Yes relation_uc prefix have p_nonzero: "p> 0" by metis
    from PrEx1 prefix construct_canonical_env2  prefix 
      have LHS: "PrExec ?Z A (CP) True = p" by auto
    
    from No relation_uc p_nonzero prefix have "p \<noteq> PrExecT ?Z S P t" by blast
    moreover have "PrExecT ?Z S P t = PrExec ?Z S P True"
      using construct_canonical_env2 prefix   by simp
    ultimately have RHS: "PrExec ?Z S P True \<noteq> p" by simp

    from LHS RHS  have "PrExec ?Z A (CP) True \<noteq> PrExec ?Z S P True" by arith
    from this Eq show "False" by blast
  qed
qed

end

section "Relating UC to RHP"

abbreviation RHPrel
  where
  "RHPrel (t:: 't itself) W W' \<equiv> 
        (\<forall> m :: 't . prefix m \<longrightarrow>  (W \<leadsto> m \<longleftrightarrow> W' \<leadsto> m))"

abbreviation RHP
  where
  "RHP C (t:: 't itself) \<equiv> \<forall> P . case (C P) of (Some CP) \<Rightarrow>  RRgen (RHPrel (t:: 't itself)) (CP) P
                                          | None \<Rightarrow> True                                  
"

context UC 
begin

theorem RHPtoUC:
  fixes C ::"('uc,'uc) comp"
  fixes ttype :: "('t \<times> real) itself"
  assumes A: "RHP C ttype"
  shows "\<forall> (P::'uc prgm) . case (C P) of (Some CP) \<Rightarrow> CP UC-emulates P | None \<Rightarrow> True"
using RSCHPtoUC assms 
  by (smt (z3) UC.relation_uc not_Some_eq option.simps(4) option.simps(5)) 

theorem UCtoRHP:
  fixes C ::"('uc,'uc) comp"
  fixes ttype :: "('t \<times> real) itself"
  assumes A1: "\<forall> (P::'uc prgm) . case (C P) of (Some CP) \<Rightarrow> CP UC-emulates P | None \<Rightarrow> True"
  shows "RHP C ttype"
proof (rule ccontr)
  assume CF: "\<not> (RHP C ttype)"
  then show "False" 
  proof -
    from CF obtain P  where  CF':"
          \<not>( case C P of None \<Rightarrow> True
          | Some CP \<Rightarrow>
              \<forall>A. \<exists>S. \<forall>m :: ('t \<times> real). prefix m \<longrightarrow>
                          A >< CP \<leadsto> m = S >< P \<leadsto> m)" by auto
    hence "\<exists> CP . C P = Some CP"   using option.simps(4) by fastforce
    then obtain CP where SomeCP: "C P  = Some (CP::'uc prgm)" by auto
    from CF' SomeCP have "\<not>(\<forall>A. \<exists>S. \<forall>m :: ('t \<times> real). prefix m \<longrightarrow>
                          A >< CP \<leadsto> m = S >< P \<leadsto> m)" by auto
    then obtain A where  NotRSCHP: "\<forall> (S::'uc ctxt).
      (\<exists> m :: ('t \<times> real) . prefix m \<and>  (A >< CP \<leadsto> m) \<noteq> (S >< P \<leadsto> m))" by auto

    from A1 SomeCP have "CP UC-emulates P "  by (smt (verit, del_insts) option.simps(5)) 
    then obtain S where Eq: "\<forall> (Z::'env) . (PrExec Z A (CP) True = PrExec Z S P True)" by blast
    from NotRSCHP have "(\<exists>  (t::'t) (p::real) . prefix (t,p) \<and> ((A >< (CP) \<leadsto> (t,p)) \<noteq> (S >< P \<leadsto> (t,p))))" by auto 
    then obtain  t :: "'t" and p :: "real" and AY and AN and PY and PN
      where prefix_full: "prefix (t,p)" 
      and Yes:"AY >< PY \<leadsto> (t,p)"
      and No: "\<not>(AN >< PN \<leadsto> (t,p))"
      and Dunno: "(AY  = A \<and> PY = CP \<and> AN = S \<and> PN = P)
                 \<or>(AN  = A \<and> PN = CP \<and> AY = S \<and> PY = P)"
      by metis
    from prefix_full prefix_iff_trace_is_prefix have prefix: "prefix t" by simp

    let ?Z = "Zcan t"
    from Yes relation_uc prefix have PrEx1: "PrExecT ?Z AY PY t = p" by metis
    from Yes relation_uc prefix have p_nonzero: "p> 0" by metis
    from PrEx1 prefix construct_canonical_env2  prefix 
      have LHS: "PrExec ?Z AY PY True = p" by auto
    
    from No relation_uc p_nonzero prefix have "p \<noteq> PrExecT ?Z AN PN t" by blast
    moreover have "PrExecT ?Z AN PN t = PrExec ?Z AN PN True"
      using construct_canonical_env2 prefix   by simp
    ultimately have RHS: "PrExec ?Z AN PN True \<noteq> p" by simp

    from LHS RHS  have "PrExec ?Z AY PY True \<noteq> PrExec ?Z AN PN True" by arith
    from this Eq Dunno show "False" by fastforce 
  qed
qed

end

section "Translating UC results to programming languages"

lemma RRGen_is_transitive [simp,trans]:
  fixes P1::"('b) prgm"
  fixes P2::"('i) prgm"
  fixes P3::"('r) prgm"
  assumes trans: "\<forall> a b c . rel12 a b \<and> rel23 b c \<longrightarrow> rel13 a c"
  assumes A: "RRgen rel12 P1 P2"
  assumes B: "RRgen rel23 P2 P3"
 shows  "RRgen rel13 P1 P3"
proof
  fix A
  from A obtain S2 where R1: "rel12 (A >< P1) (S2 >< P2)" by auto
  from B obtain S3 where R2: "rel23 (S2 >< P2) (S3 >< P3)" by auto
  from R1 R2 trans have R3: "rel13 (A >< P1) (S3 >< P3)" by simp
  then show  "\<exists> S. rel13 (A >< P1) (S >< P3)" by auto
qed

(* First, we need transitivity for RSCHPrel. *)
lemma RHPrel [simp,trans]:
  fixes ttype :: "('t \<times> real) itself" 
  assumes A1:"RHPrel ttype a b"
  assumes A2:"RHPrel ttype b c"
  shows "RHPrel ttype a c"
using A1 A2 by blast   

(* Second, for RHP compilers. *)
lemma RHPbind_trans [simp,trans]:
  fixes ttype :: "('t \<times> real) itself" 
  fixes C1 ::"('a, 'b) comp"  
  fixes C2 ::"('b, 'c) comp"   
  assumes A1:"RHP C1 ttype "
  assumes A2:"RHP C2 ttype "
  shows "RHP ((\<lambda> x. ( C1 x) >>= C2)::('a, 'c) comp)  ttype"
(*
shows "RHP (\<lambda> x. bind (C1 x) C2)  ttype" *)
proof
  fix P
  show "case bind (C1 P) C2 of None \<Rightarrow> True
         | Some CP \<Rightarrow>
             \<forall>A. \<exists>S. \<forall>m::('t \<times> real). prefix m \<longrightarrow>
                         A >< CP \<leadsto> m = S >< P \<leadsto> m" 
  
  proof (cases "bind (C1 P) C2")
    case None
    then show ?thesis by simp
  next
    case SomeC1P:(Some C2P)
    then have "\<exists> C1P . (C1 P) = Some C1P \<and> (C2 C1P) = Some C2P" by (meson bind_eq_Some_conv) 
    then obtain C1P where 
        C1P: "C1 P = Some C1P"
      and  C2P: "C2 C1P = Some C2P"   
      by auto
    from C1P A1 have "\<forall>A. \<exists>S. \<forall>m::('t \<times> real). prefix m \<longrightarrow>
                         A >< C1P \<leadsto> m = S >< P \<leadsto> m"  by (smt (verit, best) option.simps(5)) 
    from this C2P A2 have "\<forall>A. \<exists>S. \<forall>m::('t \<times> real). prefix m \<longrightarrow>
                         A >< C2P \<leadsto> m = S >< P \<leadsto> m"  by (smt (verit, best) option.simps(5))
    thus ?thesis using C1P C2P by (smt (verit, best) SomeC1P option.simps(5)) 
  qed 
qed


context UC
begin

theorem implementUC:
  fixes UCC::"('uc,'uc) comp" (* This can be seen as one for more UC results. *)
  fixes C1 ::"('b ,'uc) comp"  
  fixes C2 ::"('uc,'r ) comp"  
  fixes ttype :: "('t \<times> real) itself"  
  assumes AUCC: "\<forall> (P::'uc prgm) . case UCC P of (Some UCCP) \<Rightarrow> (UCCP) UC-emulates P | None \<Rightarrow> True"
  assumes AC1:  "RHP C1 ttype"
  assumes AC2:  "RHP C2 ttype"
  shows "RHP (\<lambda> x. C1 x \<bind> UCC \<bind> C2)   ttype"
proof-
  from UCtoRHP AUCC have ACUCC: "RHP UCC ttype" by simp
  from RHPbind_trans AC1 ACUCC have CM: "RHP (\<lambda> x. C1 x \<bind> UCC) ttype" by simp
  let ?C1UCC = "(\<lambda> x. C1 x \<bind> UCC)"
  from CM AC2 RHPbind_trans[of ?C1UCC C2] have "RHP (\<lambda> y . ?C1UCC y \<bind> C2) ttype" by simp
  thus "RHP (\<lambda> x. C1 x \<bind> UCC \<bind> C2)   ttype" by auto  
qed


end

(*
fun Behav :: "'a whle \<Rightarrow> 't set"
  where
    "Behav(W) = { t . W \<leadsto> t }"

abbreviation program_agree
  where
 "program_agree P1 P2 (ttype:: 't itself) \<equiv> 
     \<forall> T::'t set. ((\<exists> A1 . Behav(A1 >< P1) = T) = (\<exists> A2 . Behav(A2 >< P2) = T))
"
*)

abbreviation program_agree
  where
  "program_agree P1 P2 ttype \<equiv> \<exists> C . (C P1) = Some P2 \<and> RHP C ttype"


theorem (in UC) UCcompiler1:
  fixes ttype :: "('t \<times> real) itself"  
  fixes Pb::"'b prgm"
  fixes Pr::"'r prgm"
  fixes pi::"'uc prgm"
  fixes F ::"'uc prgm"  
  fixes C:: "('b,'r) comp"
  assumes FuncAgree: "program_agree Pb F ttype"
  assumes ProtAgree: "program_agree pi Pr ttype" 
  assumes Cdef1: "C Pb = Some Pr"
  assumes Cdef2: "\<forall> x. x \<noteq> Pb \<longrightarrow> C x = None" 
  (* Direction \<Longrightarrow> *)
  assumes AUCC': "pi UC-emulates F"
  shows "RHP C ttype"
proof -
  fix P A 
  obtain C1 where C1agree: "(C1 Pb) = Some F" and
                  C1RHP: "RHP (C1::('b,'uc) comp) ttype" using FuncAgree by blast  
  obtain C2 where C2agree: "(C2 pi) = Some Pr" and
                  C2RHP: "RHP (C2::('uc,'r) comp) ttype" using ProtAgree by blast
  define UCC where UCCdef: "UCC \<equiv> \<lambda>x ::'uc prgm . if x = F then Some (pi::'uc prgm) else None"  
  have AUCC:
    "\<forall> (P::'uc prgm) . case UCC P of (Some UCCP) \<Rightarrow> (UCCP) UC-emulates P | None \<Rightarrow> True"
    using AUCC' UCemulates_reflexive UCCdef by auto
  let ?bigC= " (\<lambda> (x::'b prgm). C1 x \<bind> UCC \<bind> C2) :: ('b,'r) comp"
  have RHP: "RHP (?bigC) ttype" using
        implementUC AUCC C1RHP C2RHP 
    by blast
  let ?smallC = "\<lambda> x. if x = Pb then ?bigC x else None"
  have CisSmallC: "\<forall> x . C x = ?smallC x"
  proof 
    fix x
    have "C x = ?bigC x" when X: "x=Pb" 
      using C1agree C2agree UCCdef Cdef1 X  by auto 
    moreover
    have "C x = None" when notX: "x\<noteq>Pb"
      using Cdef2 notX by auto
    ultimately
    show "C x = ?smallC x" by simp   
  qed
  then have "RHP ?smallC ttype"  using RHP by simp
  from this CisSmallC show ?thesis by auto
qed

(*
theorem(in UC) CompRCimplCompUC :
  fixes tt::"('t\<times>real) itself"
  fixes C::"('p,'r) comp"
  assumes RHCC:"RHP C ttype"
  fixes P::"'p prgm"
  fixes pi::"'uc prgm"
  fixes F ::"'uc prgm"
  assumes FuncAgree: "program_agree P F ttype"
  assumes ProtAgree: "program_agree pi (C P) ttype"
  shows "pi UC-emulates F"
proof
  fix A::"'uc ctxt"
  show "\<exists> S . (\<forall> Z . PrExec Z A pi True = PrExec Z S F True)" proof
    have "\<exists> A' . (Behav(A' >< C P)) = (Behav(A >< pi)::('t\<times>real) set)"
      using ProtAgree by auto
    then obtain A' where
      ProtBehavEq:"Behav(A' >< C P) = (Behav(A >< pi)::('t\<times>real) set)" by auto
    then obtain S' where  BehavInd:"Behav(A' >< C P) = Behav(S' >< P)"
      using RHCC by blast
    hence "\<exists> S . poly_time S F \<and> (Behav(S >< F)) = (Behav(S' >< P)::('t\<times>real\<times>nat) set)"
      using FuncAgree prog_agree_one_dir by auto
    then obtain S where PolyS:"poly_time S F"
        and FuncBehavEq:"Behav(S' >< P) = (Behav(S >< F)::('t\<times>real\<times>nat) set)" by auto
    hence "Behav(A >< pi) \<cong> Behav(S >< F)" using ProtBehavEq BehavInd by metis
    hence "\<forall> Z \<in> ZClass . PrExec Z A pi True \<approx> PrExec Z S F True" using PolyA PolyS Behav_PrExec by auto
    thus "\<exists> S . poly_time S F \<and> (\<forall> Z \<in> ZClass . PrExec Z A pi True \<approx> PrExec Z S F True)"
      using PolyS by auto
  qed
qed
*)

lemma (in UC) noUCnoRHP:
  fixes ttype :: "('t \<times> real) itself"  
  assumes A1: "\<not> (CF) UC-emulates F"
  assumes A2: "C F = Some CF"
  shows "\<not> RHP C ttype"
using A1 A2 RHPtoUC 
  by (smt (verit, del_insts) option.simps(5)) 

theorem (in UC) UCcompiler2:
  fixes ttype :: "('t \<times> real) itself"  
  fixes Pb::"'b prgm"
  fixes Pr::"'r prgm"
  fixes pi::"'uc prgm"
  fixes F ::"'uc prgm"  
  assumes AA2: "program_agree pi Pr ttype"
  assumes AA3: "program_agree F Pb ttype"
  assumes AA4: "program_agree Pr pi ttype"
  fixes C:: "('b,'r) comp"
  assumes AC1: "C Pb = Some Pr"
  (* Direction \<Longrightarrow> *)
  assumes ARHP: "RHP C ttype"
  shows "pi UC-emulates F"
proof(rule ccontr)
  assume notUC: "\<not> pi UC-emulates F"
  then show False
  proof-
  obtain C1b where C1bagree: "(C1b F) = Some Pb" and
                  C1bRHP: "RHP C1b ttype" using AA3 by blast
  obtain C2 where C2agree: "(C2 pi) = Some Pr" and
                  C2RHP: "RHP C2 ttype" using AA2 by blast
  obtain C2b where C2bagree: "(C2b Pr) = Some pi" and
                  C2bRHP: "RHP C2b ttype" using AA4 by blast

  define UCC where "UCC \<equiv> \<lambda>x ::'uc prgm . if x = F then Some (pi::'uc prgm) else None" (* Note was x before *)
  
  from notUC UCC_def have "\<not> pi UC-emulates F" by presburger
  from this UCC_def RSCHPtoUC' obtain A where  " \<forall> S . \<exists>m::'t \<times> real.
               prefix m \<and> 
               A >< pi \<leadsto>m  \<noteq>  S >< F \<leadsto> m" by metis
  from this UCC_def obtain A where  Last: " \<forall> S . \<exists>m::'t \<times> real.
               prefix m \<and> 
               A >< pi \<leadsto>m  \<noteq>  S >< F \<leadsto> m" by metis

  have "\<exists> Cr . \<forall> S . \<exists>m::'t \<times> real. prefix m \<and> 
               Cr >< Pr \<leadsto> m  \<noteq>  S >< F \<leadsto> m" 
  proof-
    from C2bRHP C2bagree have
      Side1: "\<forall>A. \<exists>S. \<forall>m::'t \<times> real . prefix m \<longrightarrow> A >< pi \<leadsto> m = S >< Pr \<leadsto> m" by (smt (verit, del_insts) option.simps(5)) 
    from C2RHP C2agree have
      Side2: "\<forall>A. \<exists>S. \<forall>m::'t \<times> real . prefix m \<longrightarrow> A >< Pr \<leadsto> m = S >< pi \<leadsto> m" by (smt (verit, del_insts) option.simps(5)) 
    from Side1 Side2 Last show ?thesis  by meson
  qed
  then obtain Cr where  "\<forall> S . \<exists>m::'t \<times> real. prefix m \<and> Cr >< Pr \<leadsto> m  \<noteq>  S >< F \<leadsto> m" 
    by meson
    
  hence NoSim: "\<forall> S . \<exists>m::'t \<times> real.
               prefix m \<and> 
               Cr >< Pr \<leadsto> m  \<noteq>  S >< F \<leadsto> m" using C2agree by blast

  from ARHP AC1 obtain Cb where 
    Bla1:"\<forall> m::'t \<times> real. prefix m \<longrightarrow> Cr >< Pr \<leadsto> m = Cb >< Pb \<leadsto> m" by (smt (verit, del_insts) option.simps(5))
  from C1bRHP C1bagree obtain S where 
    Bla2:"\<forall> m::'t \<times> real. prefix m \<longrightarrow> S >< F \<leadsto> m = Cb >< Pb \<leadsto> m" by (smt (verit, del_insts) option.simps(5))
  from NoSim obtain m::"'t \<times> real" where "prefix m" 
      and "Cr >< Pr \<leadsto> m  \<noteq>  S >< F \<leadsto> m"  by blast
  from this Bla1 Bla2 show "False" by blast
qed
qed

end
