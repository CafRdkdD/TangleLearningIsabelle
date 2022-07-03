section \<open>TangleLearning\<close>

theory TangleLearning
  imports Main 
          Parity_Game.MoreCoinductiveList
          Parity_Game.ParityGame
          Parity_Game.Strategy
          Parity_Game.Attractor
          Parity_Game.AttractingStrategy
          Parity_Game.WinningRegion
          Parity_Game.WinningStrategy
begin

type_synonym 'a Tangle = "'a set \<times> 'a Strategy"

type_synonym 'a AttrState = "'a set \<times> 'a Edge set"

subsection \<open>Utilities and auxiliary lemmas\<close>

lemma (in vm_path) vm_path_infinite_in_no_deadends_game:
  assumes "\<forall>v \<in> V. \<not> deadend v"
  shows "\<not> lfinite P"
proof
  assume lf:"lfinite P"
  then have "deadend (llast P)" 
    using finite_llast_deadend by blast
  then show "False" using assms lf
    by (meson finite_llast_V)
qed

locale PG = ParityGame +
  assumes finite_V: "finite V"
begin

lemma finite_E[simp]: "finite E" using finite_V valid_edge_set 
  by (simp add: finite_subset)

definition strategy_to_edge_set :: "'a Strategy \<Rightarrow> 'a Edge set" where
"strategy_to_edge_set \<sigma> = {(v,w) \<in> E. \<sigma> v = w}"

definition winning_prio :: " 'a set \<Rightarrow> nat" where
"winning_prio V' = Min (\<omega> ` (V' \<inter> V)) "

definition winning_prio_nodes :: "'a set \<Rightarrow> 'a set" where
"winning_prio_nodes V' = {v \<in> (V' \<inter> V). \<omega> v = winning_prio V'}"

abbreviation prio_winner :: "nat \<Rightarrow> Player" where 
"prio_winner a \<equiv> (if even a then Even else Odd)"

definition node_winner :: "'a \<Rightarrow> Player" where
"node_winner v = prio_winner (\<omega> v)"

definition nodes_winner :: " 'a set \<Rightarrow> Player" where
"nodes_winner V' = prio_winner (winning_prio V')"

lemma subgame_PG: "PG (subgame V')"
proof (unfold_locales)
  show "E\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub> \<times> V\<^bsub>subgame V'\<^esub>" using subgame_Digraph[unfolded Digraph_def].
  show "V0\<^bsub>subgame V'\<^esub> \<subseteq> V\<^bsub>subgame V'\<^esub>" unfolding subgame_def using valid_player0_set by auto
  show "finite (\<omega>\<^bsub>subgame V'\<^esub> ` V\<^bsub>subgame V'\<^esub>)" by simp
  show "finite V\<^bsub>subgame V'\<^esub>" using finite_V finite_subset subgame_V by blast
qed


subsection \<open>Closed subset and dominion\<close>

definition closed :: "'a set \<Rightarrow> Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
"closed V' p \<sigma> \<equiv> V' \<subseteq> V \<and> V' \<noteq> {} \<and>
                ParityGame.strategy (subgame V') p \<sigma> \<and>
                (\<forall>v \<in> V'.
                  (\<not> Digraph.deadend (subgame V') v) \<and>
                  (v \<in> VV p** \<longrightarrow> (\<forall>w. (v \<rightarrow> w) \<longrightarrow> w \<in> V')))"


lemma strategy_in_subgame_with_no_deadends:
  assumes "ParityGame.strategy (subgame V') p \<sigma>"
          "\<forall>v \<in> V'.\<not> Digraph.deadend (subgame V') v"
        shows "\<forall>v \<in> V'. v \<in> VV p \<longrightarrow> \<sigma> v \<in> V'" and 
              "\<forall>v \<in> V'. v \<in> VV p \<longrightarrow> v \<rightarrow>\<^bsub>(subgame V')\<^esub> \<sigma> v" 
proof (goal_cases)
  case 1
  show ?case proof
    fix v assume in_V':"v \<in> V'"
    have "v \<in> VV p \<longrightarrow> v \<in> ParityGame.VV (subgame V') p"
      using in_V' by force
    moreover have "v \<in> ParityGame.VV (subgame V') p \<longrightarrow> \<sigma> v \<in> V'"
      using assms(1,2) subgame_strategy_stays_in_subgame in_V' by blast
    ultimately show "v \<in> VV p \<longrightarrow> \<sigma> v \<in> V'" by auto
  qed
next
  case 2
  show ?case proof
    fix v assume in_V':"v \<in> V'"
    have subgame_VV:"v \<in> VV p \<longrightarrow> v \<in> ParityGame.VV (subgame V') p"
      using in_V' by force
    then have "v \<in> VV p \<and> \<not>Digraph.deadend (subgame V') v \<longrightarrow> v \<rightarrow> \<sigma> v" 
      using assms(1)  ParityGame.strategy_def subgame_E  subgame_ParityGame by blast
    then show "v \<in> VV p \<longrightarrow> v \<rightarrow>\<^bsub>(subgame V')\<^esub> \<sigma> v" 
      using assms(1,2) in_V' subgame_ParityGame subgame_VV ParityGame.strategy_def 
      by blast
  qed
qed

lemma vmc_path_in_closed_subgame_lset:
  assumes "closed V' p \<sigma>" "v0 \<in> V'" "vmc_path G P v0 p \<sigma>"
  shows "lset P \<subseteq> V'"
proof -
  define T where "T = V - V'"
  have "V' \<inter> T = {}" using T_def by auto
  moreover have "\<forall>v. (v \<in> V' \<and> \<not>deadend v \<and> v \<in> VV p) \<longrightarrow> \<sigma> v \<in> V'" 
    using assms(1) closed_def strategy_in_subgame_with_no_deadends(1) by auto
  moreover have "\<forall>v w. (v \<in> V' \<and> \<not>deadend v \<and> v \<in> VV p** \<and> v \<rightarrow> w) \<longrightarrow> w \<in> V'"
    using assms(1) closed_def by blast
  moreover have "lset P \<inter> T = {}" 
    using calculation closed_def assms
    by (smt (verit) DiffI Player.simps disjoint_eq_subset_Compl in_mono 
      order.trans vmc_path.vmc_path_lset_induction_simple vmc_path_no_deadend.v0_conforms 
      vmc_path_no_deadend.v0_edge_w0 vmc_path_no_deadend.v0_no_deadend)
  ultimately show "lset P \<subseteq> V'"
    using valid_path_in_V vm_path.P_valid assms(3) vmc_path_def T_def
    by (metis Diff_eq_empty_iff Int_Diff Int_absorb2)
qed

text \<open>Assuming a player @{term p} with a strategy @{term \<sigma>}, a set of 
  nodes @{term D} is called a dominion if: 
  1) D is closed w.r.t. to \<sigma>: p always chooses successor according to \<sigma> and all 
  nodes of p' in D along with their successors are contained in D, and 
  2) winning for player p: if p is Even, then the highest priority appearing 
  infinitely often in a path in D is even, vice versa.
\<close>
definition dominion :: "'a set \<Rightarrow> Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where
"dominion D p \<sigma> \<equiv> closed D p \<sigma> \<and>
                  (\<forall>v \<in> D. winning_strategy p \<sigma> v)"

lemma dominion_is_closed[simp]:"dominion D p \<sigma> \<Longrightarrow> closed D p \<sigma>" 
  unfolding dominion_def by auto

lemma dominion_subset_of_winning_region:
  assumes "dominion D p \<sigma>" "strategy p \<sigma>"
  shows "D \<subseteq> winning_region p"
proof 
  fix v assume in_D: "v \<in> D"
  have "v \<in> V" 
    using assms(1) dominion_def closed_def by (meson in_D subsetD)
  moreover have "winning_strategy p \<sigma> v" 
    using assms(1) dominion_def by (simp add: in_D)
  ultimately show "v \<in> winning_region p" 
    using assms(2) dominion_def by (simp add: in_D in_mono winning_regionI)
qed


subsection \<open>Tangle\<close>

inductive_set reachable_by :: "'a \<Rightarrow> 'a set" for u where
refl: "u \<in> V \<Longrightarrow> u \<in> reachable_by u" |
trans: "v \<in> reachable_by u \<Longrightarrow> v \<rightarrow> w \<Longrightarrow> w \<in> reachable_by u"

lemma valid_path_reachability_aux:
  assumes "valid_path P" "n < llength P"
  shows "n + j < llength P \<Longrightarrow> (P $ (n + j)) \<in> reachable_by (P $ n)"
proof (induction j)
  case 0
  have "(P $ n) \<in> V" using assms(1,2) valid_path_finite_in_V by auto
  then show ?case apply(auto) 
    using reachable_by.refl by auto
next
  case (Suc j) 
  have "Suc (n + j)  < llength P" using "Suc"(2) by simp
  then show ?case apply(auto)
    using assms(1) valid_path_edges reachable_by.trans Suc.IH
    by (metis Suc_llength plus_enat_simps(1))
qed

lemma valid_path_reachability:
  assumes "valid_path P" "n\<le>n'" "n' < llength P"
  shows "(P $ n') \<in> reachable_by (P $ n)"
proof -
  obtain j where n': "n'=n+j" using assms
    using nat_le_iff_add by blast
  from valid_path_reachability_aux[OF \<open>valid_path P\<close>, of n j] show ?thesis
    using assms unfolding n' 
    by (metis enat_le_plus_same(1) order_le_less_trans plus_enat_simps(1))
qed

text \<open>Strategy defined subgame: similar to @{term subgame} but only takes edges that corresponds 
to a strategy @{term \<sigma>}\<close>

definition subgame_strategy :: "'a set  \<Rightarrow> Player \<Rightarrow> 'a Strategy \<Rightarrow> ('a,'b) ParityGame_scheme" where
"subgame_strategy V' p \<sigma> = G\<lparr>verts := V \<inter> V',
                             arcs := (E \<inter> (V' \<times> V')) - {(u, v)|u v. u \<in> VV p \<and> \<sigma> u \<noteq> v},
                             player0 := V0 \<inter> V'\<rparr>"


definition scc :: "'a set \<Rightarrow> bool" where
"scc V' = (\<forall>v \<in> V'. \<forall>w \<in> V'.  w \<in> reachable_by v) "

definition tangle :: "'a set \<Rightarrow> Player \<Rightarrow> 'a Strategy \<Rightarrow> bool" where 
"tangle V' p \<sigma> \<equiv> V' \<subseteq> V \<and> V' \<noteq> {} \<and>
               ParityGame.strategy (subgame V') p \<sigma> \<and> 
               PG.scc (subgame_strategy V' p \<sigma>) V' \<and>
               (\<forall>v \<in> V'. 
                (\<not> Digraph.deadend (subgame V') v) \<and>
                (\<forall>P. vmc_path G P v p \<sigma> \<and> lset P \<subseteq> V' \<longrightarrow> winning_path p P))"

lemma unescapable_tangle_is_dominion:
  assumes "tangle T p \<sigma>"
          "\<forall>e \<in> T. e \<in> VV p** \<longrightarrow> (\<forall>f. (e \<rightarrow> f) \<longrightarrow> f \<in> T)"
  shows "dominion T p \<sigma>"
  unfolding dominion_def
proof (rule conjI)
  have "T \<subseteq> V" 
    using tangle_def[of T p \<sigma>] assms(1) by blast
  moreover have "\<forall>v \<in> T. \<not> Digraph.deadend (subgame T) v"
    using tangle_def[of T p \<sigma>] assms(1) by auto
  moreover have "ParityGame.strategy (subgame T) p \<sigma>" 
    using tangle_def[of T p \<sigma>] assms(1) by auto
  ultimately show closed:"closed T p \<sigma>"
    using closed_def assms(1,2) tangle_def by auto

  then have "\<forall>v \<in> T. \<forall>P. vmc_path G P v p \<sigma> \<longrightarrow> lset P \<subseteq> T"
    using vmc_path_in_closed_subgame_lset by auto
  then have "\<forall>v \<in> T. \<forall>P. vmc_path G P v p \<sigma> \<longrightarrow> winning_path p P"
    using tangle_def assms(1) by simp
  then show "\<forall>v \<in> T. winning_strategy p \<sigma> v"
    using winning_strategyI by blast
qed 

lemma SCC_in_closed_subset:
  assumes "closed V' p \<sigma>"     
  shows "\<exists>S. S \<subseteq> V' \<and> PG.scc (subgame V') S"
proof 
  have "\<exists>v0. v0 \<in> V'" using assms closed_def by auto
  then obtain v0 where in_V':"v0 \<in> V'" by auto
  interpret G': PG "subgame V'" using subgame_PG.

  have "G'.strategy p \<sigma>" using assms closed_def by auto
  then have "\<exists>P. vmc_path (subgame V') P v0 p \<sigma>" 
    using closed_def in_V' assms G'.strategy_conforming_path_exists_single
    by (metis subgame_V')
  then obtain P' where P'_vmc: "vmc_path (subgame V') P' v0 p \<sigma>"
    by auto

  have inf:"\<not>lfinite P'" proof-
    have "vm_path (subgame V') P' v0" 
      using vmc_path_def P'_vmc by metis
    moreover have "\<forall>v \<in> V\<^bsub>subgame V'\<^esub>. \<not>Digraph.deadend (subgame V') v "
      using closed_def assms  by auto
    ultimately show "\<not>lfinite P'" 
      using vm_path.vm_path_infinite_in_no_deadends_game by metis
  qed
  have lset:"lset P' \<subseteq> V'" 
    using assms closed_def P'_vmc vmc_path_def
    by (metis G'.valid_path_in_V subgame_V' vm_path.P_valid )

  text \<open>Define a function mapping indices to vertices in the path and prove it is infinite\<close>
  define f where "f i = (P' $ i)" for i
    have "range f \<subseteq> V'" unfolding f_def 
      using lset lset_nth_member_inf[OF inf] by blast
    moreover have "finite V'" 
      using finite_V closed_def assms(1) finite_subset by metis
    ultimately have "finite (range f)" using finite_subset by auto
    then obtain n0 where n0:"\<not> (finite {n. f n = f n0})"
      using pigeonhole_infinite[of UNIV f] by auto


  define W where "W = {k. \<forall>n. k \<in> lset (ldropn n P')}"
  have not_empty: "\<exists>k . k \<in> W" proof-
    define k where "k = f n0"
    have "P' $ n0 = k" unfolding f_def k_def 
      using inf by (simp add: infinite_small_llength)
    moreover {
      fix a assume "P' $ a = k"
      have "\<exists>n' > a. f n' = k" unfolding k_def 
        using n0 infinite_nat_iff_unbounded by auto
      then have "\<exists>n' > a. P' $ n' = k" unfolding f_def
        using inf by (simp add:infinite_small_llength)
    }
    ultimately have "\<forall>n. k \<in> lset (ldropn n P')" 
      using inf by (simp add: index_infinite_set)
    thus ?thesis unfolding W_def by blast
  qed

  obtain n1 where n1:"(\<not> finite {n. f n = f n0}) \<and> (n1 > n0) \<and> n1 \<in> {n. f n = f n0}"
    using pigeonhole_infinite[of UNIV f] n0
    by (meson infinite_nat_iff_unbounded)
  have n0_n1_eq: "P' $ n0 = P' $  n1" 
    using n1 by (simp add: f_def)
  moreover have P'_valid:"G'.valid_path P'" 
    using P'_vmc vmc_path_def by (metis  vm_path.P_valid)
  ultimately have "(P' $ n1) \<in> G'.reachable_by (P' $ n0)" 
    using G'.valid_path_reachability inf by auto

  define cycle where "cycle = ltake (Suc (n1 - n0)) (ldrop n0 P')"
  have "lhd cycle = P' $ n0" using cycle_def 
    by (metis eSuc_enat inf infinite_small_llength ldrop_enat ldropn_Suc_conv_ldropn lhd_LCons 
        ltake_eSuc_LCons)
  moreover have "llast cycle = P' $ n1" unfolding cycle_def using inf n1
    by (metis enat.distinct(2) enat_ord_simps(2) infinite_small_llength lappend_ltake_ldrop 
        less_Suc_eq lfinite_ldrop llast_ltake llength_ltake' lnth_lappend not_less_eq 
        the_enat.simps)
  ultimately have "lhd cycle = llast cycle" 
    using n0_n1_eq by auto

  have "G'.valid_path cycle" unfolding cycle_def using P'_valid
    by (metis G'.valid_path_drop G'.valid_path_prefix  ldrop_enat ltake_is_lprefix)
  have subset_V': "lset cycle \<subseteq> V'" 
    using in_lset_ldropnD in_V' lset W_def cycle_def Coinductive_List.lset_ltake
    by (metis ldrop_enat subset_eq)

    oops

lemma dominion_contains_a_tangle:
  assumes "dominion D p \<sigma>"
  shows "\<exists>T. T \<subseteq> D \<and> tangle T p \<sigma>"
  unfolding tangle_def
proof 
  oops


subsection \<open>Tangle Learning\<close>

definition attr_strategy_step :: "Player \<Rightarrow> 'a AttrState \<Rightarrow> 'a AttrState" where
"attr_strategy_step p Z = (let A = fst Z; \<sigma> = snd Z;
                          step_V = {v \<in> V - A. \<not>deadend v \<and> 
                            (v \<in> VV p   \<longrightarrow> (\<exists>w. v\<rightarrow>w \<and> w \<in> A)) \<and>
                            (v \<in> VV p** \<longrightarrow> (\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> A))};
                          step_\<sigma> = {e|v w e. v \<in> V - A \<and> \<not>deadend v \<and> 
                            (v \<in> VV p \<longrightarrow> (\<exists>w. v\<rightarrow>w \<and> w \<in> A) \<and>  (e = (v,w))) \<and>
                            (v \<in> VV p** \<longrightarrow> (\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> A))}
                               in (A \<union> step_V, \<sigma> \<union> step_\<sigma>))"

function attractor_strategy :: "Player \<Rightarrow> 'a AttrState \<Rightarrow> 'a AttrState" where
"attractor_strategy p Z = (let Z' = attr_strategy_step p Z in 
                         (if Z = Z' then Z else attractor_strategy p Z'))"
  by auto

definition escapes :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"escapes p T = {v|u v. (u \<rightarrow> v) \<and> (u \<in> T \<inter> VV p**) \<and> (v \<in> V - T)}"

definition player_tangles :: "Player \<Rightarrow> 'a Tangle set \<Rightarrow> 'a Tangle set" where
"player_tangles p T = {(Tp,\<sigma>)|Tp \<sigma>. (Tp,\<sigma>) \<in> T \<and> tangle Tp p \<sigma>}"

definition tangle_attr_step :: "Player \<Rightarrow> 'a AttrState \<Rightarrow> 'a Tangle set \<Rightarrow> 'a AttrState" where
"tangle_attr_step p Z T = (let attracted = {(Tp,\<sigma>') \<in> player_tangles p T. 
                                     (escapes p Tp \<noteq> {}) \<and> 
                                     (escapes p Tp \<subseteq> (fst Z))} in 
                             (Union (Domain attracted), 
                              Finite_Set.fold (\<lambda>A B. (strategy_to_edge_set A) \<union> B) {} (Range attracted)))"

function tangle_attractor :: "Player \<Rightarrow> 'a AttrState \<Rightarrow> 'a Tangle set \<Rightarrow> 'a AttrState" where
"tangle_attractor p Z T = (let attr_step = attr_strategy_step p Z;
                               t_attr_step = tangle_attr_step p Z T;
                               Z' = (fst attr_step \<union> fst t_attr_step,
                                     snd attr_step \<union> snd t_attr_step) in
                        (if Z = Z' then Z else tangle_attractor p Z' T))"
  by auto

function extract_tangles :: "'a set \<Rightarrow> 'a Edge set \<Rightarrow> 'a Tangle set" where
"extract_tangles Z \<sigma> = "
end 

function search :: "'a ParityGame \<Rightarrow> 'a Tangle set \<Rightarrow> 'a set set \<times> 'a set" where
"search P T =  (if (V\<^bsub>P\<^esub> = {} \<or> \<not>PG P) then ({},{}) 
                else (let prio = winning_prio P V\<^bsub>P\<^esub>;
                           \<alpha> = nodes_winner P V\<^bsub>P\<^esub>; 
                           v = winning_prio_nodes P V\<^bsub>P\<^esub>;
                           Z = PG.tangle_attractor P \<alpha> v T in
                     (if )) 
                ) "

function solve :: "'a ParityGame \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<times> 'a set set \<times> 'a set \<times> 'a set" where
"solve P T W0 W1 = (if (V\<^bsub>P\<^esub> = {} \<or> \<not>PG P) then ({},{},{},{}) 
                     else search  )"
end