theory FSA_Semantics
  imports FSA_Metamodel
begin

inductive rtrancl_path :: "'a rel \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a rel"
where
  base: "rtrancl_path r x [] x"
| step: "(x, y) \<in> r \<Longrightarrow> rtrancl_path r y ys z \<Longrightarrow> rtrancl_path r x (y # ys) z"

lemma rtranclp_eq_rtrancl_path: "(x, y) \<in> r\<^sup>* \<longleftrightarrow> (\<exists>xs. rtrancl_path r x xs y)"
proof
  show "\<exists>xs. rtrancl_path r x xs y" if "(x, y) \<in> r\<^sup>*"
    using that
  proof (induct rule: converse_rtrancl_induct)
    case base
    have "rtrancl_path r y [] y" by (rule rtrancl_path.base)
    then show ?case ..
  next
    case (step x z)
    from \<open>\<exists>xs. rtrancl_path r z xs y\<close>
    obtain xs where "rtrancl_path r z xs y" ..
    with \<open>(x, z) \<in> r\<close> have "rtrancl_path r x (z # xs) y"
      by (rule rtrancl_path.step)
    then show ?case ..
  qed
  show "(x, y) \<in> r\<^sup>*" if "\<exists>xs. rtrancl_path r x xs y"
  proof -
    from that obtain xs where "rtrancl_path r x xs y" ..
    then show ?thesis
    proof induct
      case (base x)
      show ?case
        by (rule rtrancl.rtrancl_refl)
    next
      case (step x y ys z)
      from \<open>(x, y) \<in> r\<close> \<open>(y, z) \<in> r\<^sup>*\<close> show ?case
        by (rule converse_rtrancl_into_rtrancl)
    qed
  qed
qed


definition fsa_trans_sem :: "Automaton \<Rightarrow> string rel" ("\<lbrakk>_\<rbrakk>\<^sub>T")
  where "fsa_trans_sem A = {(s\<^sub>1, s\<^sub>2). \<exists> t\<in>set (transitions A). from t = s\<^sub>1 \<and> to t = s\<^sub>2}"

definition fsa_init_sem :: "Automaton \<Rightarrow> string set" ("\<lbrakk>_\<rbrakk>\<^sub>I")
  where "\<lbrakk>A\<rbrakk>\<^sub>I = {State.name s |s. s \<in> set (states A) \<and> initial s}"

definition fsa_sem :: "Automaton \<Rightarrow> string rel" ("\<lbrakk>_\<rbrakk>\<^sub>\<A>")
  where "\<lbrakk>A\<rbrakk>\<^sub>\<A> = {(sa, s). s \<in> \<lbrakk>A\<rbrakk>\<^sub>I} O \<lbrakk>A\<rbrakk>\<^sub>T\<^sup>*"

definition reachable :: "Automaton \<Rightarrow> State \<Rightarrow> bool" where
"reachable A s' = (\<exists> s p. s \<in> \<lbrakk>A\<rbrakk>\<^sub>I \<and> rtrancl_path \<lbrakk>A\<rbrakk>\<^sub>T s p (State.name s'))"

lemma invariant_rtrancl_path:
  assumes "\<lbrakk>A\<rbrakk>\<^sub>I \<subseteq> I" "\<lbrakk>A\<rbrakk>\<^sub>T `` I \<subseteq> I" "s \<in> \<lbrakk>A\<rbrakk>\<^sub>I" "rtrancl_path \<lbrakk>A\<rbrakk>\<^sub>T s p s'"
  shows "s' \<in> I"
  using assms(3-4)
proof (induct p arbitrary: s s')
  case Nil
  then show ?case
    by (metis assms(1) list.distinct(1) rtrancl_path.cases subset_eq)
next
  case (Cons s\<^sub>0 p)
  have "(s, s\<^sub>0) \<in> \<lbrakk>A\<rbrakk>\<^sub>T"
    using Cons.prems(2) rtrancl_path.cases by fastforce
  hence "s\<^sub>0 \<in> I"
    using Cons.prems(1) assms(1) assms(2) by blast
  then show ?case
    by (metis Cons.prems(1) Cons.prems(2) Image_closed_trancl Image_iff assms(1) assms(2) rtranclp_eq_rtrancl_path subset_iff)
qed

lemma unreachable_by_invariant:
  assumes "\<lbrakk>A\<rbrakk>\<^sub>I \<subseteq> I" "\<lbrakk>A\<rbrakk>\<^sub>T `` I \<subseteq> I" "State.name s' \<notin> I"
  shows "\<not> (reachable A s')"
  by (meson assms(1) assms(2) assms(3) invariant_rtrancl_path reachable_def)

end