import tactic

/- see the document doc/categorya.pdf -/

/- 1 Definition Section -/

def div (a:ℕ)(b:ℕ) := ∃c:ℕ, b=a*c
infix ` | `:55 := div

def is_even (a:ℕ) := 2|a 

def is_prime (a:ℕ) := a≠1 ∧ 
(∀b:ℕ, b|a → (b=1 ∨ b=a))

def is_gcd (a:ℕ)(b:ℕ)(d:ℕ) := d|a ∧ d|b 
∧ (∀c:ℕ, (c|a ∧ c|b) → c|d)

def is_coprime (a:ℕ)(b:ℕ) := is_gcd a b 1

/- 2 Lemma Section -/

/- 2.1 Divison Part -/

lemma one_div_nat (a:ℕ) : 1|a := -- Lemma 6
begin
  use a,
  simp,
end

lemma nat_div_zero (a:ℕ) : a|0 := -- Lemma 7
begin
  use 0,
  simp,
end

lemma div_refl (a:ℕ): a|a := -- Lemma 8
begin
  use 1,
  simp,
end

lemma div_trans (a:ℕ)(b:ℕ)(c:ℕ): 
a|b → b|c → a|c := -- Lemma 9
begin
  intros f g,
  rw div at f g ⊢,
  cases f with c1,
  cases g with c2,
  use c1*c2,
  rw f_h at g_h,
  rw g_h,
  rw mul_assoc,
end

/- Divison Algorithm/ Quotient Remainder Theorem -/

lemma div_alg_exist (a:ℕ)(b:ℕ):
b≠0 → (∃q:ℕ, ∃r:ℕ, r<b ∧ a=b*q+r) := --Lemma 34
begin
  intro f,

  /- prove by induction on a -/
  induction a with d hd,

  /- the case for a=0 -/
  use 0,
  use 0,
  split,
  cases b,
  exfalso,
  apply f,
  refl,
  exact nat.succ_pos',
  simp,

  /- the inductive case:
  assume that a=bq+r and r < b 
  we want to find q' and r' 
  such that a+1=bq'+r'
  -/
  cases hd with q hq,
  cases hq with r hr,

  /- there are two subcases -/
  /- Subcase I: r+1 < b -/
  by_cases r+1<b,
  /- Let q'=q and r'=r+1 -/
  use q,
  use r+1,
  cases hr with hrp hrq,
  split,
  exact h,
  rw ← nat.one_add,
  rw hrq,
  rw add_comm,
  rw add_assoc,

  /- Subcase II: r+1 ≥ b -/
  simp at h,
  /- Since r+1 ≥ b, r+1=b+k for some k -/
  have t:=nat.exists_eq_add_of_le h,
  cases t with k tk,
  /- Then we prove that k must be 0 -/
  cases hr with hrp hrq,
  have u: 0<1 := zero_lt_one,
  have v: r+0+1<b+1 := nat.add_succ_lt_add hrp u,
  rw add_assoc at v,
  rw zero_add at v,
  rw tk at v,
  simp at v,
  rw nat.lt_iff_add_one_le at v,
  simp at v,
  /- Let r'=0 and q'=q+1 -/
  use q+1,
  use 0,
  rw v at tk,
  simp at tk,
  split,
  cases b,
  exfalso,
  apply f,
  refl,
  apply nat.succ_pos',
  simp,
  rw ←  nat.one_add,
  rw hrq,
  rw ← tk,
  ring,
end  

lemma div_alg_unique (a:ℕ)(b:ℕ):
∀ q1 :ℕ, ∀ r1:ℕ, ∀ q2:ℕ, ∀ r2:ℕ, 
(r1<b ∧ r2<b ∧ a=b*q1+r1 ∧ a=b*q2+r2)→ 
(q1=q2 ∧ r1=r2):= -- Lemma 34
begin
  sorry,
end

/- 2.2 Prime Part-/

lemma zero_is_not_prime: 
is_prime(0)→false := -- Lemma 19
begin
  intro h,
  cases h with p q,
  have t:=q(2),
  have u:=nat_div_zero(2),
  have v:=t(u),
  cases v with s t,
  simp at s,
  exact s,
  simp at t,
  exact t,
end

lemma one_is_not_prime:
is_prime(1)→false := -- Lemma 20
begin
  intro f,
  have t:=f.1,
  apply t,
  refl,
end

/- 2.3 GCD Part-/

lemma gcd_of_a_div_b (a:ℕ)(b:ℕ):
a|b → is_gcd a b a := -- Lemma 27
begin
  intro f,
  split,
  apply div_refl,
  split,
  exact f,
  intro c,
  intro g,
  cases g with p q,
  exact p,
end

lemma gcd_of_nat_zero (a:ℕ): 
is_gcd a 0 a := -- Lemma 28
begin
  have t: a|0 := nat_div_zero a, 
  apply gcd_of_a_div_b a 0 t,
end 

lemma gcd_of_one_nat (b:ℕ):
is_gcd 1 b 1 := -- Lemma 29
begin
  have t: 1|b := one_div_nat b, 
  apply gcd_of_a_div_b 1 b t,
end

lemma prime_coprime (a:ℕ)(p:ℕ):
(¬p|a) → is_prime p → is_coprime a p 
:= -- Lemma 33
begin
  intros f g,
  cases g with gp gq,
  split,
  exact one_div_nat a,
  split,
  exact one_div_nat p,
  intro c,
  intro g,
  cases g with g1 g2,
  have gqc:=gq c,
  have h:= gqc g2,
  cases h with hp hq,
  rw hp,
  exact one_div_nat 1,
  rw hq at g1,
  exfalso,
  cc,
end 