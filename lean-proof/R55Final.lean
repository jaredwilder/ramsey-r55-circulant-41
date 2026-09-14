set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 200000000

def deg (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) : Nat := (V.filter (e v)).length

def degSumOn (e : Nat → Nat → Bool) (L W : List Nat) : Nat :=
  (L.map (fun v => deg e v W)).sum

theorem deg_cons_self (e : Nat → Nat → Bool) (a : Nat) (t : List Nat) (h : e a a = false) :
    deg e a (a :: t) = deg e a t := by
  unfold deg; simp [List.filter_cons, h]

theorem deg_cons_other (e : Nat → Nat → Bool) (a v : Nat) (t : List Nat) :
    deg e v (a :: t) = (if e v a = true then 1 else 0) + deg e v t := by
  unfold deg
  by_cases h : e v a = true
  · simp [List.filter_cons, h]; omega
  · simp [List.filter_cons, h]

/-- summing a pointwise sum splits -/
theorem sum_map_add (f g : Nat → Nat) : ∀ L : List Nat,
    (L.map (fun v => f v + g v)).sum = (L.map f).sum + (L.map g).sum := by
  intro L; induction L with
  | nil => simp
  | cons a t ih => simp [ih]; omega

/-- an indicator sum counts the filter -/
theorem sum_indicator (p : Nat → Bool) : ∀ L : List Nat,
    (L.map (fun v => if p v = true then 1 else 0)).sum = (L.filter p).length := by
  intro L; induction L with
  | nil => simp
  | cons a t ih =>
    by_cases h : p a = true
    · simp [List.filter_cons, h, ih]; omega
    · simp [List.filter_cons, h, ih]

/-- symmetry lets the incoming count be read as the outgoing degree -/
theorem filter_symm (e : Nat → Nat → Bool) (hs : ∀ x y, e x y = e y x) (a : Nat) :
    ∀ L : List Nat, (L.filter (fun v => e v a)).length = deg e a L := by
  intro L
  unfold deg
  have : (fun v => e v a) = (e a) := by funext v; exact hs v a
  rw [this]

/-- ⭐ THE HANDSHAKE, over vertex lists: for a symmetric relation that is loop-free on the
    list, the degree sum is TWICE the degree sum of the tail plus twice a vertex degree —
    hence even, by induction. -/
theorem degSum_even (e : Nat → Nat → Bool) (hs : ∀ x y, e x y = e y x) :
    ∀ L : List Nat, (∀ v ∈ L, e v v = false) → degSumOn e L L % 2 = 0 := by
  intro L
  induction L with
  | nil => intro _; simp [degSumOn]
  | cons a t ih =>
    intro hloop
    have hself : e a a = false := hloop a (by simp)
    have htail : ∀ v ∈ t, e v v = false := fun v hv => hloop v (by simp [hv])
    have hih := ih htail
    have hstep : degSumOn e (a :: t) (a :: t) = 2 * deg e a t + degSumOn e t t := by
      unfold degSumOn
      simp only [List.map_cons, List.sum_cons]
      rw [deg_cons_self e a t hself]
      have hmap : (t.map (fun v => deg e v (a :: t)))
                = (t.map (fun v => (if e v a = true then 1 else 0) + deg e v t)) := by
        apply List.map_congr_left
        intro v _
        exact deg_cons_other e a v t
      rw [hmap, sum_map_add (fun v => if e v a = true then 1 else 0) (fun v => deg e v t) t,
          sum_indicator (fun v => e v a) t, filter_symm e hs a t]
      omega
    rw [hstep]
    omega

theorem degSum_even_control : degSumOn (fun a b => a != b) [0,1,2] [0,1,2] = 6 := by decide

/-- the complement degree, with the vertex itself excluded -/
def ndeg (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) : Nat :=
  (V.filter (fun u => (v != u) && ! e v u)).length

/-- in a duplicate-free list containing v, the elements other than v number one fewer -/
theorem count_others (v : Nat) : ∀ L : List Nat, L.Nodup → v ∈ L →
    (L.filter (fun u => v != u)).length = L.length - 1 := by
  intro L
  induction L with
  | nil => intro _ h; simp at h
  | cons a t ih =>
    intro hnd hmem
    rcases List.mem_cons.mp hmem with rfl | hv
    · have hnot : v ∉ t := (List.nodup_cons.mp hnd).1
      have : (t.filter (fun u => v != u)) = t := by
        apply List.filter_eq_self.mpr
        intro x hx
        simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
        intro hxe; exact hnot (hxe ▸ hx)
      simp [List.filter_cons, this]
    · have hnd' : t.Nodup := (List.nodup_cons.mp hnd).2
      have hne : v ≠ a := by
        intro he; exact (List.nodup_cons.mp hnd).1 (he ▸ hv)
      have hlen : 1 ≤ t.length := by
        cases t with
        | nil => simp at hv
        | cons _ _ => simp
      simp [List.filter_cons, hne, ih hnd' hv]
      omega

/-- so the two degrees split the rest of the list exactly -/
theorem deg_split (e : Nat → Nat → Bool) (v : Nat) : ∀ L : List Nat, L.Nodup → v ∈ L →
    e v v = false → deg e v L + ndeg e v L = L.length - 1 := by
  intro L hnd hmem hloop
  unfold deg ndeg
  have hsplit : ∀ M : List Nat,
      (M.filter (e v)).length + (M.filter (fun u => (v != u) && ! e v u)).length
        = (M.filter (fun u => v != u)).length := by
    intro M
    induction M with
    | nil => simp
    | cons a t ih =>
      by_cases hva : v = a
      · subst hva
        simp [List.filter_cons, hloop, ih]
      · by_cases hea : e v a = true
        · simp [List.filter_cons, hea, hva, ih]; omega
        · simp [List.filter_cons, hea, hva, ih]; omega
  rw [hsplit L, count_others v L hnd hmem]
/-- THE REORDERING LEMMA the parity sharpening needs.
    A clique drawn from anywhere in the vertex list can be re-assembled with a chosen vertex
    inserted in its correct position, as a SUBLIST, with one more element and the same
    membership.  Proved by induction on the list, splitting on the two Sublist constructors. -/
theorem insert_sublist : ∀ (V : List Nat) (K : List Nat) (v : Nat),
    K.Sublist V → v ∈ V → v ∉ K →
    ∃ K' : List Nat, K'.Sublist V ∧ K'.length = K.length + 1 ∧
      (∀ x, x ∈ K' ↔ (x = v ∨ x ∈ K)) := by
  intro V
  induction V with
  | nil => intro K v _ hv _; simp at hv
  | cons a t ih =>
    intro K v hsub hv hnk
    rcases List.sublist_cons_iff.mp hsub with hKt | ⟨K0, rfl, hK0⟩
    · rcases List.mem_cons.mp hv with rfl | hvt
      · exact ⟨v :: K, List.Sublist.cons₂ v hKt, by simp, by intro x; simp⟩
      · obtain ⟨K', hs, hl, hm⟩ := ih K v hKt hvt hnk
        exact ⟨K', List.Sublist.cons a hs, hl, hm⟩
    · have hva : v ≠ a := by
        intro he; exact hnk (by simp [he])
      have hvt : v ∈ t := by
        rcases List.mem_cons.mp hv with he | h
        · exact absurd he hva
        · exact h
      have hnk0 : v ∉ K0 := fun h => hnk (List.mem_cons_of_mem a h)
      obtain ⟨K', hs, hl, hm⟩ := ih K0 v hK0 hvt hnk0
      refine ⟨a :: K', List.Sublist.cons₂ a hs, by simp [hl], ?_⟩
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact Or.inr (by simp)
        · rcases (hm x).mp hx' with rfl | hx''
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem a hx'')
      · intro hx
        rcases hx with rfl | hx'
        · exact List.mem_cons_of_mem a ((hm x).mpr (Or.inl rfl))
        · rcases List.mem_cons.mp hx' with rfl | hx''
          · simp
          · exact List.mem_cons_of_mem a ((hm x).mpr (Or.inr hx''))

def IsClique (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = true

def IsIndep (e : Nat → Nat → Bool) (L : List Nat) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, a ≠ b → e a b = false

/-- IsClique quantifies over MEMBERS, so it transfers across any membership equivalence. -/
theorem clique_congr (e : Nat → Nat → Bool) (K K' : List Nat)
    (h : ∀ x, x ∈ K' ↔ x ∈ K) (hK : IsClique e K) : IsClique e K' := by
  intro a ha b hb hab
  exact hK a ((h a).mp ha) b ((h b).mp hb) hab

theorem indep_congr (e : Nat → Nat → Bool) (K K' : List Nat)
    (h : ∀ x, x ∈ K' ↔ x ∈ K) (hK : IsIndep e K) : IsIndep e K' := by
  intro a ha b hb hab
  exact hK a ((h a).mp ha) b ((h b).mp hb) hab

/-- ⭐ THE COMBINED STEP: a clique found anywhere in the list, together with a vertex adjacent
    to all of it, yields a clique one larger that IS a sublist of the list. -/
theorem insert_clique (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (V K : List Nat) (v : Nat)
    (hsub : K.Sublist V) (hv : v ∈ V) (hnk : v ∉ K)
    (hadj : ∀ x ∈ K, e v x = true) (hK : IsClique e K) :
    ∃ K' : List Nat, K'.Sublist V ∧ K'.length = K.length + 1 ∧ IsClique e K' := by
  obtain ⟨K', hs, hl, hm⟩ := insert_sublist V K v hsub hv hnk
  refine ⟨K', hs, hl, ?_⟩
  refine clique_congr e (v :: K) K' (fun x => ?_) ?_
  · rw [hm x, List.mem_cons]
  · exact fun a ha b hb hab => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact hadj b hb'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rw [hsymm]; exact hadj a ha'
        · exact hK a ha' b hb' hab

theorem insert_indep (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (V K : List Nat) (v : Nat)
    (hsub : K.Sublist V) (hv : v ∈ V) (hnk : v ∉ K)
    (hadj : ∀ x ∈ K, e v x = false) (hK : IsIndep e K) :
    ∃ K' : List Nat, K'.Sublist V ∧ K'.length = K.length + 1 ∧ IsIndep e K' := by
  obtain ⟨K', hs, hl, hm⟩ := insert_sublist V K v hsub hv hnk
  refine ⟨K', hs, hl, ?_⟩
  refine indep_congr e (v :: K) K' (fun x => ?_) ?_
  · rw [hm x, List.mem_cons]
  · exact fun a ha b hb hab => by
      rcases List.mem_cons.mp ha with rfl | ha'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · exact absurd rfl hab
        · exact hadj b hb'
      · rcases List.mem_cons.mp hb with rfl | hb'
        · rw [hsymm]; exact hadj a ha'
        · exact hK a ha' b hb' hab

def ArrowsOn (e : Nat → Nat → Bool) (V : List Nat) (s t : Nat) : Prop :=
  (∃ K : List Nat, K.Sublist V ∧ K.length = s ∧ IsClique e K) ∨
  (∃ K : List Nat, K.Sublist V ∧ K.length = t ∧ IsIndep e K)

/-- the Nodup-restricted sufficiency relation the degree argument needs -/
def SufficesN (m s t : Nat) : Prop :=
  ∀ (e : Nat → Nat → Bool), (∀ x y, e x y = e y x) →
    ∀ V : List Nat, V.Nodup → m ≤ V.length → ArrowsOn e V s t

/-- ⭐ THE DEGREE BOUND: if the arrows relation FAILS on V, then every vertex's degree is
    strictly below m.  This is where the reordering lemma earns its place — the vertex is
    arbitrary, not the head. -/
theorem degree_bound (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (m s t : Nat) (hs : 1 ≤ s) (hm : SufficesN m (s-1) t)
    (V : List Nat) (hnd : V.Nodup) (hfail : ¬ ArrowsOn e V s t)
    (v : Nat) (hv : v ∈ V) (hloop : e v v = false) :
    deg e v V < m := by
  rcases Nat.lt_or_ge (deg e v V) m with hlt | hge
  · exact hlt
  exfalso
  have hA : (V.filter (e v)).Nodup := hnd.filter _
  have hlen : m ≤ (V.filter (e v)).length := hge
  rcases hm e hsymm (V.filter (e v)) hA hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hin⟩
  · have hsubV : K.Sublist V := hsub.trans (List.filter_sublist)
    have hadj : ∀ x ∈ K, e v x = true := by
      intro x hx
      have := hsub.subset hx
      simpa using (List.mem_filter.mp this).2
    have hnk : v ∉ K := by
      intro h
      have := hadj v h
      rw [hloop] at this
      exact Bool.noConfusion this
    obtain ⟨K', hs', hl', hc'⟩ := insert_clique e hsymm V K v hsubV hv hnk hadj hcl
    exact hfail (Or.inl ⟨K', hs', by omega, hc'⟩)
  · exact hfail (Or.inr ⟨K, hsub.trans (List.filter_sublist), hlk, hin⟩)

/-- the loop-free companion of a colouring: identical off the diagonal -/
def lf (e : Nat → Nat → Bool) : Nat → Nat → Bool := fun x y => (x != y) && e x y

theorem lf_symm (e : Nat → Nat → Bool) (hs : ∀ x y, e x y = e y x) :
    ∀ x y, lf e x y = lf e y x := by
  intro x y
  unfold lf
  rw [hs x y]
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := fun he => h he.symm
    have e1 : (x != y) = true := bne_iff_ne.mpr h
    have e2 : (y != x) = true := bne_iff_ne.mpr h'
    rw [e1, e2]

theorem lf_loopfree (e : Nat → Nat → Bool) (x : Nat) : lf e x x = false := by
  unfold lf; simp

theorem clique_lf (e : Nat → Nat → Bool) (K : List Nat) :
    IsClique e K ↔ IsClique (lf e) K := by
  constructor
  · intro h a ha b hb hab
    unfold lf; simp [hab, h a ha b hb hab]
  · intro h a ha b hb hab
    have := h a ha b hb hab
    unfold lf at this
    simp [hab] at this
    exact this

theorem indep_lf (e : Nat → Nat → Bool) (K : List Nat) :
    IsIndep e K ↔ IsIndep (lf e) K := by
  constructor
  · intro h a ha b hb hab
    unfold lf; simp [hab, h a ha b hb hab]
  · intro h a ha b hb hab
    have := h a ha b hb hab
    unfold lf at this
    simp [hab] at this
    exact this

theorem arrows_lf (e : Nat → Nat → Bool) (V : List Nat) (s t : Nat) :
    ArrowsOn e V s t ↔ ArrowsOn (lf e) V s t := by
  unfold ArrowsOn
  constructor
  · rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact Or.inl ⟨K, h1, h2, (clique_lf e K).mp h3⟩
    · exact Or.inr ⟨K, h1, h2, (indep_lf e K).mp h3⟩
  · rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact Or.inl ⟨K, h1, h2, (clique_lf e K).mpr h3⟩
    · exact Or.inr ⟨K, h1, h2, (indep_lf e K).mpr h3⟩

theorem sufficesN_lf (m s t : Nat) (h : SufficesN m s t) :
    ∀ (e : Nat → Nat → Bool), (∀ x y, e x y = e y x) →
      ∀ V : List Nat, V.Nodup → m ≤ V.length → ArrowsOn (lf e) V s t := by
  intro e hs V hnd hl
  exact (arrows_lf e V s t).mp (h e hs V hnd hl)

/-- the complement colouring, loop-free by construction -/
def ce (e : Nat → Nat → Bool) : Nat → Nat → Bool := fun x y => (x != y) && ! e x y

theorem ce_symm (e : Nat → Nat → Bool) (hs : ∀ x y, e x y = e y x) :
    ∀ x y, ce e x y = ce e y x := by
  intro x y
  unfold ce
  rw [hs x y]
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := fun he => h he.symm
    have e1 : (x != y) = true := bne_iff_ne.mpr h
    have e2 : (y != x) = true := bne_iff_ne.mpr h'
    rw [e1, e2]

theorem ce_loopfree (e : Nat → Nat → Bool) (x : Nat) : ce e x x = false := by
  unfold ce; simp

/-- a clique in the complement is an independent set in the original, and vice versa -/
theorem clique_ce (e : Nat → Nat → Bool) (K : List Nat) :
    IsClique (ce e) K ↔ IsIndep e K := by
  constructor
  · intro h a ha b hb hab
    have := h a ha b hb hab
    unfold ce at this
    simp [hab] at this
    exact this
  · intro h a ha b hb hab
    unfold ce; simp [hab, h a ha b hb hab]

theorem indep_ce (e : Nat → Nat → Bool) (K : List Nat) :
    IsIndep (ce e) K ↔ IsClique e K := by
  constructor
  · intro h a ha b hb hab
    have := h a ha b hb hab
    unfold ce at this
    simp [hab] at this
    exact this
  · intro h a ha b hb hab
    unfold ce; simp [hab, h a ha b hb hab]

/-- so the arrows relation swaps its two parameters under complementation -/
theorem arrows_ce (e : Nat → Nat → Bool) (V : List Nat) (s t : Nat) :
    ArrowsOn (ce e) V s t ↔ ArrowsOn e V t s := by
  unfold ArrowsOn
  constructor
  · rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact Or.inr ⟨K, h1, h2, (clique_ce e K).mp h3⟩
    · exact Or.inl ⟨K, h1, h2, (indep_ce e K).mp h3⟩
  · rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact Or.inr ⟨K, h1, h2, (indep_ce e K).mpr h3⟩
    · exact Or.inl ⟨K, h1, h2, (clique_ce e K).mpr h3⟩

/-- the two degrees are the two colours -/
theorem ndeg_eq_deg_ce (e : Nat → Nat → Bool) (v : Nat) (V : List Nat) :
    ndeg (lf e) v V = deg (ce e) v V := by
  unfold ndeg deg lf ce
  congr 1
  apply List.filter_congr
  intro x _
  by_cases h : v = x
  · subst h; simp
  · have e1 : (v != x) = true := bne_iff_ne.mpr h
    simp [e1]

theorem sum_map_const2 (f : Nat → Nat) (d : Nat) : ∀ L : List Nat,
    (∀ v ∈ L, f v = d) → (L.map f).sum = L.length * d := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons a t ih =>
    intro h
    have ha : f a = d := h a (by simp)
    have ht : (t.map f).sum = t.length * d := ih (fun v hv => h v (by simp [hv]))
    simp [ha, ht, Nat.succ_mul]
    omega

theorem degSumOn_regular (e : Nat → Nat → Bool) (W : List Nat) (d : Nat)
    (h : ∀ v ∈ W, deg e v W = d) : degSumOn e W W = W.length * d :=
  sum_map_const2 (fun v => deg e v W) d W h

theorem sufficesN_swap (m a b : Nat) (h : SufficesN m a b) : SufficesN m b a := by
  intro e hs V hnd hl
  exact (arrows_ce e V a b).mp (h (ce e) (ce_symm e hs) V hnd hl)

theorem gg_parity2 (m n : Nat) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hme : m % 2 = 0) (hne : n % 2 = 0) : ((m + n - 1) * (m - 1)) % 2 = 1 := by
  have h1 : (m + n - 1) % 2 = 1 := by omega
  have h2 : (m - 1) % 2 = 1 := by omega
  rw [Nat.mul_mod, h1, h2]

/-- ⭐⭐ THE PARITY SHARPENING, on the campaign's carrier. -/
theorem gg_sharpening (m n s t : Nat) (hm2 : 2 ≤ m) (hn2 : 2 ≤ n) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hme : m % 2 = 0) (hne : n % 2 = 0)
    (hm : SufficesN m (s-1) t) (hn : SufficesN n s (t-1)) :
    SufficesN (m + n - 1) s t := by
  intro e hsymm V hnd hlen
  rcases Classical.em (ArrowsOn e V s t) with hok | hfail
  · exact hok
  exfalso
  have hWsub : (V.take (m + n - 1)).Sublist V := List.take_sublist _ _
  have hWnd : (V.take (m + n - 1)).Nodup := hnd.sublist hWsub
  have hWlen : (V.take (m + n - 1)).length = m + n - 1 := by
    simp [List.length_take]; omega
  have hWfail : ¬ ArrowsOn e (V.take (m + n - 1)) s t := by
    rintro (⟨K, h1, h2, h3⟩ | ⟨K, h1, h2, h3⟩)
    · exact hfail (Or.inl ⟨K, h1.trans hWsub, h2, h3⟩)
    · exact hfail (Or.inr ⟨K, h1.trans hWsub, h2, h3⟩)
  have hlfF : ¬ ArrowsOn (lf e) (V.take (m + n - 1)) s t :=
    fun hx => hWfail ((arrows_lf e _ s t).mpr hx)
  have hceF : ¬ ArrowsOn (ce e) (V.take (m + n - 1)) t s :=
    fun hx => hWfail ((arrows_ce e _ t s).mp hx)
  have hreg : ∀ v ∈ V.take (m + n - 1), deg (lf e) v (V.take (m + n - 1)) = m - 1 := by
    intro v hv
    have hred : deg (lf e) v (V.take (m + n - 1)) < m :=
      degree_bound (lf e) (lf_symm e hsymm) m s t hs hm _ hWnd hlfF v hv (lf_loopfree e v)
    have hblue : deg (ce e) v (V.take (m + n - 1)) < n :=
      degree_bound (ce e) (ce_symm e hsymm) n t s ht (sufficesN_swap n s (t-1) hn) _ hWnd
        hceF v hv (ce_loopfree e v)
    have hsplit := deg_split (lf e) v (V.take (m + n - 1)) hWnd hv (lf_loopfree e v)
    rw [ndeg_eq_deg_ce e v (V.take (m + n - 1))] at hsplit
    omega
  have heq : degSumOn (lf e) (V.take (m + n - 1)) (V.take (m + n - 1))
           = (m + n - 1) * (m - 1) := by
    rw [degSumOn_regular (lf e) _ (m - 1) hreg, hWlen]
  have heven : degSumOn (lf e) (V.take (m + n - 1)) (V.take (m + n - 1)) % 2 = 0 :=
    degSum_even (lf e) (lf_symm e hsymm) _ (fun v _ => lf_loopfree e v)
  rw [heq] at heven
  have hodd := gg_parity2 m n hm2 hn2 hme hne
  omega

theorem extend_cliqueN (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (v : Nat) (K : List Nat) (hadj : ∀ x ∈ K, e v x = true) (hK : IsClique e K) :
    IsClique e (v :: K) := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hadj b hb'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hsymm]; exact hadj a ha'
    · exact hK a ha' b hb' hab

theorem extend_indepN (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x)
    (v : Nat) (K : List Nat) (hadj : ∀ x ∈ K, e v x = false) (hK : IsIndep e K) :
    IsIndep e (v :: K) := by
  intro a ha b hb hab
  rcases List.mem_cons.mp ha with rfl | ha'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · exact absurd rfl hab
    · exact hadj b hb'
  · rcases List.mem_cons.mp hb with rfl | hb'
    · rw [hsymm]; exact hadj a ha'
    · exact hK a ha' b hb' hab

theorem suffices_one_leftN (t : Nat) : SufficesN 1 1 t := by
  intro e _ V _ hV
  cases V with
  | nil => simp at hV
  | cons v R =>
    refine Or.inl ⟨[v], List.Sublist.cons₂ v (List.nil_sublist R), rfl, ?_⟩
    intro a ha b hb hab
    simp at ha hb; subst ha; subst hb; exact absurd rfl hab

theorem suffices_one_rightN (s : Nat) : SufficesN 1 s 1 := by
  intro e _ V _ hV
  cases V with
  | nil => simp at hV
  | cons v R =>
    refine Or.inr ⟨[v], List.Sublist.cons₂ v (List.nil_sublist R), rfl, ?_⟩
    intro a ha b hb hab
    simp at ha hb; subst ha; subst hb; exact absurd rfl hab

theorem filter_splitN (p : Nat → Bool) : ∀ L : List Nat,
    (L.filter p).length + (L.filter (fun x => ! p x)).length = L.length := by
  intro L
  induction L with
  | nil => rfl
  | cons a t ih =>
    by_cases h : p a
    · simp [List.filter, h] at *; omega
    · simp [List.filter, h] at *; omega

theorem es_recurrenceN (m n s t : Nat) (hm1 : 1 <= m) (hn1 : 1 <= n)
    (hs : 1 <= s) (ht : 1 <= t)
    (hm : SufficesN m (s-1) t) (hn : SufficesN n s (t-1)) :
    SufficesN (m + n) s t := by
  intro e hsymm V hnd hV
  cases V with
  | nil => simp at hV; omega
  | cons v R =>
    have hRnd : R.Nodup := (List.nodup_cons.mp hnd).2
    have hlen : m + n <= R.length + 1 := by simpa using hV
    have hsplit := filter_splitN (fun x => e v x) R
    have hcase : m <= (R.filter (fun x => e v x)).length
               \/ n <= (R.filter (fun x => ! e v x)).length := by omega
    rcases hcase with hA | hB
    . rcases hm e hsymm (R.filter (fun x => e v x)) (hRnd.filter _) hA with
        ⟨K, hKsub, hKlen, hKcl⟩ | ⟨K, hKsub, hKlen, hKind⟩
      . refine Or.inl ⟨v :: K, ?_, ?_, ?_⟩
        . exact List.Sublist.cons₂ v (hKsub.trans List.filter_sublist)
        . simp only [List.length_cons, hKlen]; omega
        . refine extend_cliqueN e hsymm v K ?_ hKcl
          intro x hx
          have hxA : x ∈ R.filter (fun y => e v y) := hKsub.subset hx
          simpa using (List.mem_filter.mp hxA).2
      . exact Or.inr ⟨K, (hKsub.trans List.filter_sublist).cons v, hKlen, hKind⟩
    . rcases hn e hsymm (R.filter (fun x => ! e v x)) (hRnd.filter _) hB with
        ⟨K, hKsub, hKlen, hKcl⟩ | ⟨K, hKsub, hKlen, hKind⟩
      . exact Or.inl ⟨K, (hKsub.trans List.filter_sublist).cons v, hKlen, hKcl⟩
      . refine Or.inr ⟨v :: K, ?_, ?_, ?_⟩
        . exact List.Sublist.cons₂ v (hKsub.trans List.filter_sublist)
        . simp only [List.length_cons, hKlen]; omega
        . refine extend_indepN e hsymm v K ?_ hKind
          intro x hx
          have hxB : x ∈ R.filter (fun y => ! e v y) := hKsub.subset hx
          have := (List.mem_filter.mp hxB).2
          simpa using this

/-- ⭐⭐ THE SHARPENED CHAIN: 62, not 70. -/
theorem es_chain62 : SufficesN 62 5 5 := by
  have g11 : SufficesN 1 1 1 := suffices_one_leftN 1
  have g12 : SufficesN 1 1 2 := suffices_one_leftN 2
  have g13 : SufficesN 1 1 3 := suffices_one_leftN 3
  have g14 : SufficesN 1 1 4 := suffices_one_leftN 4
  have g15 : SufficesN 1 1 5 := suffices_one_leftN 5
  have g21 : SufficesN 1 2 1 := suffices_one_rightN 2
  have g22 : SufficesN 2 2 2 := es_recurrenceN 1 1 2 2 (by omega) (by omega) (by omega) (by omega) g12 g21
  have g23 : SufficesN 3 2 3 := es_recurrenceN 1 2 2 3 (by omega) (by omega) (by omega) (by omega) g13 g22
  have g24 : SufficesN 4 2 4 := es_recurrenceN 1 3 2 4 (by omega) (by omega) (by omega) (by omega) g14 g23
  have g25 : SufficesN 5 2 5 := es_recurrenceN 1 4 2 5 (by omega) (by omega) (by omega) (by omega) g15 g24
  have g31 : SufficesN 1 3 1 := suffices_one_rightN 3
  have g32 : SufficesN 3 3 2 := es_recurrenceN 2 1 3 2 (by omega) (by omega) (by omega) (by omega) g22 g31
  have g33 : SufficesN 6 3 3 := es_recurrenceN 3 3 3 3 (by omega) (by omega) (by omega) (by omega) g23 g32
  have g34 : SufficesN 9 3 4 := gg_sharpening 4 6 3 4 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) g24 g33
  have g35 : SufficesN 14 3 5 := es_recurrenceN 5 9 3 5 (by omega) (by omega) (by omega) (by omega) g25 g34
  have g41 : SufficesN 1 4 1 := suffices_one_rightN 4
  have g42 : SufficesN 4 4 2 := es_recurrenceN 3 1 4 2 (by omega) (by omega) (by omega) (by omega) g32 g41
  have g43 : SufficesN 9 4 3 := gg_sharpening 6 4 4 3 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) g33 g42
  have g44 : SufficesN 18 4 4 := es_recurrenceN 9 9 4 4 (by omega) (by omega) (by omega) (by omega) g34 g43
  have g45 : SufficesN 31 4 5 := gg_sharpening 14 18 4 5 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) g35 g44
  have g51 : SufficesN 1 5 1 := suffices_one_rightN 5
  have g52 : SufficesN 5 5 2 := es_recurrenceN 4 1 5 2 (by omega) (by omega) (by omega) (by omega) g42 g51
  have g53 : SufficesN 14 5 3 := es_recurrenceN 9 5 5 3 (by omega) (by omega) (by omega) (by omega) g43 g52
  have g54 : SufficesN 31 5 4 := gg_sharpening 18 14 5 4 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) g44 g53
  have g55 : SufficesN 62 5 5 := es_recurrenceN 31 31 5 5 (by omega) (by omega) (by omega) (by omega) g45 g54
  exact g55

/-- ⭐ THE SPECIALISATION of the sharpened ceiling to the standard Ramsey statement.
    `SufficesN` already demands `Nodup`, so the returned 5-sublist of `List.range 62` has five
    DISTINCT vertices; this is `R(5,5) ≤ 62` in the ordinary sense. -/
theorem R55_le_62 (e : Nat → Nat → Bool) (hsymm : ∀ x y, e x y = e y x) :
    (∃ K : List Nat, K.Sublist (List.range 62) ∧ K.Nodup ∧ K.length = 5 ∧ IsClique e K) ∨
    (∃ K : List Nat, K.Sublist (List.range 62) ∧ K.Nodup ∧ K.length = 5 ∧ IsIndep e K) := by
  have hnd : (List.range 62).Nodup := List.nodup_range
  have hlen : 62 ≤ (List.range 62).length := by simp
  rcases es_chain62 e hsymm (List.range 62) hnd hlen with
    ⟨K, hs, hl, hc⟩ | ⟨K, hs, hl, hi⟩
  · exact Or.inl ⟨K, hs, hs.nodup hnd, hl, hc⟩
  · exact Or.inr ⟨K, hs, hs.nodup hnd, hl, hi⟩

/-- monotonicity for the Nodup-restricted relation -/
theorem sufficesN_mono (m m' s t : Nat) (h : m ≤ m') (hm : SufficesN m s t) :
    SufficesN m' s t := by
  intro e hsymm V hnd hV
  exact hm e hsymm V hnd (by omega)

/-- the sharpened tail -/
theorem sharpened_gives_the_tail (m : Nat) (h : 62 ≤ m) : SufficesN m 5 5 :=
  sufficesN_mono 62 m 5 5 h es_chain62

/-- and the improvement, stated as a fact about the two ceilings -/
theorem sharpening_improves : (62 : Nat) < 70 := by decide
def S : List Nat := [1,2,3,5,7,10,13,15,16,17,24,25,26,28,31,34,36,38,39,40]
def adj (i j : Nat) : Bool := ((i % 41 + 41 - j % 41) % 41) ∈ S
def nadj (i j : Nat) : Bool := ! adj i j

theorem symm_res :
    (List.range 41).all (fun a => (List.range 41).all (fun b =>
      (((a + 41 - b) % 41) ∈ S) == (((b + 41 - a) % 41) ∈ S))) = true := by decide

theorem adj_symm (x y : Nat) : adj x y = adj y x := by
  have hx : x % 41 < 41 := Nat.mod_lt _ (by decide)
  have hy : y % 41 < 41 := Nat.mod_lt _ (by decide)
  have h := List.all_eq_true.mp symm_res (x % 41) (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h (y % 41) (List.mem_range.mpr hy)
  unfold adj
  simpa using h2

theorem nadj_symm (x y : Nat) : nadj x y = nadj y x := by
  unfold nadj; rw [adj_symm x y]

def gnest (e : Nat → Nat → Bool) : Bool :=
  (List.range 41).all fun a => (List.range 41).all fun b => (! (a < b)) || (! e a b) ||
    ((List.range 41).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 41).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d) ||
        ((List.range 41).all fun f => (! (d < f)) || (! e a f) || (! e b f) || (! e c f) || (! e d f))))

theorem gnest_adj : gnest adj = true := by decide
theorem gnest_nadj : gnest nadj = true := by decide

theorem gextract (e : Nat → Nat → Bool) (h : gnest e = true)
    (a b c d f : Nat) (ha : a < 41) (hb : b < 41) (hc : c < 41) (hd : d < 41) (hf : f < 41)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hdf : d < f)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true)
    (p4 : e a d = true) (p5 : e b d = true) (p6 : e c d = true)
    (p7 : e a f = true) (p8 : e b f = true) (p9 : e c f = true) (p10 : e d f = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [hab, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [hbc, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  have h4 := List.all_eq_true.mp h3 d (List.mem_range.mpr hd)
  simp only [hcd, decide_true, Bool.not_true, p4, p5, p6, Bool.false_or] at h4
  have h5 := List.all_eq_true.mp h4 f (List.mem_range.mpr hf)
  simp only [hdf, decide_true, Bool.not_true, p7, p8, p9, p10, Bool.false_or] at h5
  exact Bool.noConfusion h5

theorem sub_range_lt {n : Nat} {K : List Nat} (h : K.Sublist (List.range n)) :
    ∀ x ∈ K, x < n := by
  intro x hx; exact List.mem_range.mp (h.subset hx)

theorem sub_range_pairwise {n : Nat} {K : List Nat} (h : K.Sublist (List.range n)) :
    K.Pairwise (· < ·) := List.Pairwise.sublist h List.pairwise_lt_range

theorem len5 {K : List Nat} (h : K.length = 5) : ∃ a b c d f, K = [a, b, c, d, f] := by
  match K, h with
  | [a, b, c, d, f], _ => exact ⟨a, b, c, d, f, rfl⟩

theorem pw5 {a b c d f : Nat} (h : ([a,b,c,d,f] : List Nat).Pairwise (· < ·)) :
    a < b ∧ b < c ∧ c < d ∧ d < f := by
  simp [List.pairwise_cons] at h
  omega

/-- ⭐ THE FLOOR, ON THE SAME CARRIER AS THE CEILING.
    41 vertices do NOT suffice for (5,5): the order-41 circulant is the counterexample. -/
theorem not_sufficesN_41 : ¬ SufficesN 41 5 5 := by
  intro hS
  have hlen : 41 ≤ (List.range 41).length := by simp
  rcases hS adj adj_symm (List.range 41) List.nodup_range hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hind⟩
  · obtain ⟨a, b, c, d, f, rfl⟩ := len5 hlk
    obtain ⟨hab, hbc, hcd, hdf⟩ := pw5 (sub_range_pairwise hsub)
    have hb5 := sub_range_lt hsub
    exact gextract adj gnest_adj a b c d f
      (hb5 a (by simp)) (hb5 b (by simp)) (hb5 c (by simp)) (hb5 d (by simp)) (hb5 f (by simp))
      hab hbc hcd hdf
      (hcl a (by simp) b (by simp) (by omega)) (hcl a (by simp) c (by simp) (by omega))
      (hcl b (by simp) c (by simp) (by omega)) (hcl a (by simp) d (by simp) (by omega))
      (hcl b (by simp) d (by simp) (by omega)) (hcl c (by simp) d (by simp) (by omega))
      (hcl a (by simp) f (by simp) (by omega)) (hcl b (by simp) f (by simp) (by omega))
      (hcl c (by simp) f (by simp) (by omega)) (hcl d (by simp) f (by simp) (by omega))
  · obtain ⟨a, b, c, d, f, rfl⟩ := len5 hlk
    obtain ⟨hab, hbc, hcd, hdf⟩ := pw5 (sub_range_pairwise hsub)
    have hb5 := sub_range_lt hsub
    have hn : ∀ x ∈ ([a,b,c,d,f] : List Nat), ∀ y ∈ ([a,b,c,d,f] : List Nat), x ≠ y →
        nadj x y = true := by
      intro x hx y hy hxy
      simp [nadj, hind x hx y hy hxy]
    exact gextract nadj gnest_nadj a b c d f
      (hb5 a (by simp)) (hb5 b (by simp)) (hb5 c (by simp)) (hb5 d (by simp)) (hb5 f (by simp))
      hab hbc hcd hdf
      (hn a (by simp) b (by simp) (by omega)) (hn a (by simp) c (by simp) (by omega))
      (hn b (by simp) c (by simp) (by omega)) (hn a (by simp) d (by simp) (by omega))
      (hn b (by simp) d (by simp) (by omega)) (hn c (by simp) d (by simp) (by omega))
      (hn a (by simp) f (by simp) (by omega)) (hn b (by simp) f (by simp) (by omega))
      (hn c (by simp) f (by simp) (by omega)) (hn d (by simp) f (by simp) (by omega))

/-! ## ⭐⭐⭐ THE FINAL BRACKET: 42 ≤ R(5,5) ≤ 62, one file, one carrier. -/

theorem bracket62 : ¬ SufficesN 41 5 5 ∧ SufficesN 62 5 5 :=
  ⟨not_sufficesN_41, es_chain62⟩

def IsExactlyN (N s t : Nat) : Prop := SufficesN N s t ∧ ¬ SufficesN (N - 1) s t

theorem exact_value_in_bracket62 (N : Nat) (h : IsExactlyN N 5 5) : 42 ≤ N ∧ N ≤ 62 := by
  obtain ⟨hsuf, hnot⟩ := h
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge N 42 with hlt | hge
    · exact absurd (sufficesN_mono N 41 5 5 (by omega) hsuf) not_sufficesN_41
    · exact hge
  · rcases Nat.lt_or_ge 62 N with hgt | hle
    · exact absurd (sufficesN_mono 62 (N - 1) 5 5 (by omega) es_chain62) hnot
    · exact hle

/-- ⛔ THE OBSTRUCTION, on this carrier: the first order the campaign cannot decide. -/
theorem frontier_obligation62 : SufficesN 43 5 5 := by
  sorry

theorem the_open_gap62 : (62 : Nat) - 42 = 20 := by decide

/-! ## ⭐ WHAT CLOSING THE OBSTRUCTION WOULD BUY — proved, and NOT assuming the obstruction.

    These are implications. They quantify the leverage of `frontier_obligation62` without
    using it: each takes the open statement as a HYPOTHESIS and says what follows. -/

/-- If 43 sufficed, the value is pinned to two orders. -/
theorem leverage_43 (h43 : SufficesN 43 5 5) (N : Nat) (hN : IsExactlyN N 5 5) :
    N = 42 ∨ N = 43 := by
  have hnot := hN.2
  have hlo : 42 ≤ N := (exact_value_in_bracket62 N hN).1
  rcases Nat.lt_or_ge 43 N with hgt | hle
  · exact absurd (sufficesN_mono 43 (N - 1) 5 5 (by omega) h43) hnot
  · omega

/-- More generally, ANY sufficient order M pins the value between 42 and M. -/
theorem leverage_general (M : Nat) (hM : SufficesN M 5 5) (N : Nat) (hN : IsExactlyN N 5 5) :
    42 ≤ N ∧ N ≤ M := by
  have hnot := hN.2
  refine ⟨(exact_value_in_bracket62 N hN).1, ?_⟩
  rcases Nat.lt_or_ge M N with hgt | hle
  · exact absurd (sufficesN_mono M (N - 1) 5 5 (by omega) hM) hnot
  · exact hle

/-- And the contrapositive direction: a witness at order M rules out every value at or below M. -/
theorem leverage_witness (M : Nat) (hM : ¬ SufficesN M 5 5) (N : Nat) (hN : IsExactlyN N 5 5) :
    M < N := by
  have hsuf := hN.1
  rcases Nat.lt_or_ge M N with hlt | hge
  · exact hlt
  · exact absurd (sufficesN_mono N M 5 5 hge hsuf) hM

/-- The two levers named together: the campaign's own ends recover the bracket through them. -/
theorem levers_recover_the_bracket (N : Nat) (hN : IsExactlyN N 5 5) : 42 ≤ N ∧ N ≤ 62 :=
  ⟨Nat.lt_iff_add_one_le.mp (leverage_witness 41 not_sufficesN_41 N hN),
   (leverage_general 62 es_chain62 N hN).2⟩

/-! ## ⭐ A SECOND PARAMETER PAIR, kernel-checked: R(4,5) ≥ 25.

    The order-24 circulant `Cay(Z_24, ±{1,2,4,8,9,15,16,20,22,23})` has no red K4 and no blue
    K5, so 24 does not suffice for (4,5). Same carrier, same definitions as everything above. -/

def S24 : List Nat := [1, 2, 4, 8, 9, 15, 16, 20, 22, 23]

def adj24 (i j : Nat) : Bool := S24.contains ((i % 24 + 24 - j % 24) % 24)

/-- symmetry, as a BOUNDED check the kernel can decide -/
theorem adj24_symm_res :
    (List.range 24).all (fun i => (List.range 24).all (fun j => adj24 i j == adj24 j i))
      = true := by decide

def nadj24 (i j : Nat) : Bool := ! adj24 i j

theorem nadj24_symm_res :
    (List.range 24).all (fun i => (List.range 24).all (fun j => nadj24 i j == nadj24 j i))
      = true := by decide

/-- no red K4: a guarded nest over the 24 vertices, work follows partial cliques -/
def noK4_24 : Bool :=
  (List.range 24).all (fun a =>
    (List.range 24).all (fun b => ! (b < a && adj24 a b) ||
      (List.range 24).all (fun c => ! (c < b && adj24 a c && adj24 b c) ||
        (List.range 24).all (fun d => ! (d < c && adj24 a d && adj24 b d && adj24 c d)))))

/-- no blue K5: the same nest on the complement, five deep -/
def noI5_24 : Bool :=
  (List.range 24).all (fun a =>
    (List.range 24).all (fun b => ! (b < a && nadj24 a b) ||
      (List.range 24).all (fun c => ! (c < b && nadj24 a c && nadj24 b c) ||
        (List.range 24).all (fun d => ! (d < c && nadj24 a d && nadj24 b d && nadj24 c d) ||
          (List.range 24).all (fun e => ! (e < d && nadj24 a e && nadj24 b e && nadj24 c e
                                            && nadj24 d e))))))

theorem noK4_24_holds : noK4_24 = true := by decide
theorem noI5_24_holds : noI5_24 = true := by decide

/-- NEGATIVE CONTROLS, load-bearing: the same nests must be able to say NO. -/
def ctrlK4 : Bool :=
  (List.range 24).all (fun a =>
    (List.range 24).all (fun b => ! (b < a && true) ||
      (List.range 24).all (fun c => ! (c < b && true && true) ||
        (List.range 24).all (fun d => ! (d < c && true && true && true)))))

theorem ctrlK4_is_false : ctrlK4 = false := by decide

/-- the witness is genuinely 4-chromatic-ish: it DOES contain a red triangle, so the K4 nest is
    not vacuously true from an empty red graph -/
def hasRedTriangle24 : Bool :=
  (List.range 24).any (fun a =>
    (List.range 24).any (fun b => b < a && adj24 a b &&
      (List.range 24).any (fun c => c < b && adj24 a c && adj24 b c)))

theorem hasRedTriangle24_holds : hasRedTriangle24 = true := by decide

/-- and it DOES contain a blue 4-set, so the I5 nest is not vacuous either -/
def hasBlue4_24 : Bool :=
  (List.range 24).any (fun a =>
    (List.range 24).any (fun b => b < a && nadj24 a b &&
      (List.range 24).any (fun c => c < b && nadj24 a c && nadj24 b c &&
        (List.range 24).any (fun d => d < c && nadj24 a d && nadj24 b d && nadj24 c d))))

theorem hasBlue4_24_holds : hasBlue4_24 = true := by decide

/-! ## ⭐ FLOOR CERTIFICATES FOR THE CHAIN'S OWN INTERMEDIATES.
    Every value the sharpened chain passes through now has a witness BELOW it in this
    same file, so each intermediate is bracketed on both sides. -/

def S35 : List Nat := [1, 5, 8, 12]

def a35 (i j : Nat) : Bool := S35.contains ((i % 13 + 13 - j % 13) % 13)

def n35 (i j : Nat) : Bool := ! a35 i j

theorem a35_symm_res :
    (List.range 13).all (fun i => (List.range 13).all (fun j => a35 i j == a35 j i)) = true := by decide

def noK3_35 : Bool :=
  (List.range 13).all (fun a =>
    (List.range 13).all (fun b => ! (b < a && a35 a b) ||
    (List.range 13).all (fun c => ! (c < b && a35 a c && a35 b c)
    )))

theorem noK3_35_holds : noK3_35 = true := by decide

def noI5_35 : Bool :=
  (List.range 13).all (fun a =>
    (List.range 13).all (fun b => ! (b < a && n35 a b) ||
    (List.range 13).all (fun c => ! (c < b && n35 a c && n35 b c) ||
    (List.range 13).all (fun d => ! (d < c && n35 a d && n35 b d && n35 c d) ||
    (List.range 13).all (fun e => ! (e < d && n35 a e && n35 b e && n35 c e && n35 d e)
    )))))

theorem noI5_35_holds : noI5_35 = true := by decide

def hasRed_35 : Bool := (List.range 13).any (fun a => (List.range 13).any (fun b => b < a && a35 a b))

theorem hasRed_35_holds : hasRed_35 = true := by decide

def hasBlue_35 : Bool := (List.range 13).any (fun a => (List.range 13).any (fun b => b < a && n35 a b))

theorem hasBlue_35_holds : hasBlue_35 = true := by decide

def S44 : List Nat := [1, 2, 4, 8, 9, 13, 15, 16]

def a44 (i j : Nat) : Bool := S44.contains ((i % 17 + 17 - j % 17) % 17)

def n44 (i j : Nat) : Bool := ! a44 i j

theorem a44_symm_res :
    (List.range 17).all (fun i => (List.range 17).all (fun j => a44 i j == a44 j i)) = true := by decide

def noK4_44 : Bool :=
  (List.range 17).all (fun a =>
    (List.range 17).all (fun b => ! (b < a && a44 a b) ||
    (List.range 17).all (fun c => ! (c < b && a44 a c && a44 b c) ||
    (List.range 17).all (fun d => ! (d < c && a44 a d && a44 b d && a44 c d)
    ))))

theorem noK4_44_holds : noK4_44 = true := by decide

def noI4_44 : Bool :=
  (List.range 17).all (fun a =>
    (List.range 17).all (fun b => ! (b < a && n44 a b) ||
    (List.range 17).all (fun c => ! (c < b && n44 a c && n44 b c) ||
    (List.range 17).all (fun d => ! (d < c && n44 a d && n44 b d && n44 c d)
    ))))

theorem noI4_44_holds : noI4_44 = true := by decide

def hasRed_44 : Bool := (List.range 17).any (fun a => (List.range 17).any (fun b => b < a && a44 a b))

theorem hasRed_44_holds : hasRed_44 = true := by decide

def hasBlue_44 : Bool := (List.range 17).any (fun a => (List.range 17).any (fun b => b < a && n44 a b))

theorem hasBlue_44_holds : hasBlue_44 = true := by decide



/-! ## ⭐ THE MISSING BRIDGES — audit 8's finding, closed.
    Each nest fact is LIFTED to the carrier, exactly as `not_sufficesN_41` does.
    The bound variables are a b c d f g: `e` is the relation's name and would shadow it,
    which is precisely the error the first generated attempt made. -/

theorem lenq3 {K : List Nat} (h : K.length = 3) : ∃ a b c, K = [a, b, c] := by
  match K, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

theorem pwq3 {a b c : Nat} (h : ([a, b, c] : List Nat).Pairwise (· < ·)) :
    a < b ∧ b < c := by
  simp [List.pairwise_cons] at h
  omega

theorem lenq4 {K : List Nat} (h : K.length = 4) : ∃ a b c d, K = [a, b, c, d] := by
  match K, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem pwq4 {a b c d : Nat} (h : ([a, b, c, d] : List Nat).Pairwise (· < ·)) :
    a < b ∧ b < c ∧ c < d := by
  simp [List.pairwise_cons] at h
  omega

theorem lenq5 {K : List Nat} (h : K.length = 5) : ∃ a b c d f, K = [a, b, c, d, f] := by
  match K, h with
  | [a, b, c, d, f], _ => exact ⟨a, b, c, d, f, rfl⟩

theorem pwq5 {a b c d f : Nat} (h : ([a, b, c, d, f] : List Nat).Pairwise (· < ·)) :
    a < b ∧ b < c ∧ c < d ∧ d < f := by
  simp [List.pairwise_cons] at h
  omega

def gn_24_4 (e : Nat → Nat → Bool) : Bool :=
  (List.range 24).all fun a => (List.range 24).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 24).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 24).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d)))

theorem gx_24_4 (e : Nat → Nat → Bool) (h : gn_24_4 e = true)
    (a b c d : Nat) (ha : a < 24) (hb : b < 24) (hc : c < 24) (hd : d < 24)
    (o0 : a < b) (o1 : b < c) (o2 : c < d)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true) (p4 : e a d = true) (p5 : e b d = true) (p6 : e c d = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [o0, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [o1, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  have h4 := List.all_eq_true.mp h3 d (List.mem_range.mpr hd)
  simp only [o2, decide_true, Bool.not_true, p4, p5, p6, Bool.false_or] at h4
  exact Bool.noConfusion h4

def gn_24_5 (e : Nat → Nat → Bool) : Bool :=
  (List.range 24).all fun a => (List.range 24).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 24).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 24).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d) ||
      ((List.range 24).all fun f => (! (d < f)) || (! e a f) || (! e b f) || (! e c f) || (! e d f))))

theorem gx_24_5 (e : Nat → Nat → Bool) (h : gn_24_5 e = true)
    (a b c d f : Nat) (ha : a < 24) (hb : b < 24) (hc : c < 24) (hd : d < 24) (hf : f < 24)
    (o0 : a < b) (o1 : b < c) (o2 : c < d) (o3 : d < f)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true) (p4 : e a d = true) (p5 : e b d = true) (p6 : e c d = true) (p7 : e a f = true) (p8 : e b f = true) (p9 : e c f = true) (p10 : e d f = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [o0, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [o1, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  have h4 := List.all_eq_true.mp h3 d (List.mem_range.mpr hd)
  simp only [o2, decide_true, Bool.not_true, p4, p5, p6, Bool.false_or] at h4
  have h5 := List.all_eq_true.mp h4 f (List.mem_range.mpr hf)
  simp only [o3, decide_true, Bool.not_true, p7, p8, p9, p10, Bool.false_or] at h5
  exact Bool.noConfusion h5

def gn_35_3 (e : Nat → Nat → Bool) : Bool :=
  (List.range 13).all fun a => (List.range 13).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 13).all fun c => (! (b < c)) || (! e a c) || (! e b c))

theorem gx_35_3 (e : Nat → Nat → Bool) (h : gn_35_3 e = true)
    (a b c : Nat) (ha : a < 13) (hb : b < 13) (hc : c < 13)
    (o0 : a < b) (o1 : b < c)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [o0, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [o1, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  exact Bool.noConfusion h3

def gn_35_5 (e : Nat → Nat → Bool) : Bool :=
  (List.range 13).all fun a => (List.range 13).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 13).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 13).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d) ||
      ((List.range 13).all fun f => (! (d < f)) || (! e a f) || (! e b f) || (! e c f) || (! e d f))))

theorem gx_35_5 (e : Nat → Nat → Bool) (h : gn_35_5 e = true)
    (a b c d f : Nat) (ha : a < 13) (hb : b < 13) (hc : c < 13) (hd : d < 13) (hf : f < 13)
    (o0 : a < b) (o1 : b < c) (o2 : c < d) (o3 : d < f)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true) (p4 : e a d = true) (p5 : e b d = true) (p6 : e c d = true) (p7 : e a f = true) (p8 : e b f = true) (p9 : e c f = true) (p10 : e d f = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [o0, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [o1, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  have h4 := List.all_eq_true.mp h3 d (List.mem_range.mpr hd)
  simp only [o2, decide_true, Bool.not_true, p4, p5, p6, Bool.false_or] at h4
  have h5 := List.all_eq_true.mp h4 f (List.mem_range.mpr hf)
  simp only [o3, decide_true, Bool.not_true, p7, p8, p9, p10, Bool.false_or] at h5
  exact Bool.noConfusion h5

def gn_44_4 (e : Nat → Nat → Bool) : Bool :=
  (List.range 17).all fun a => (List.range 17).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 17).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 17).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d)))

theorem gx_44_4 (e : Nat → Nat → Bool) (h : gn_44_4 e = true)
    (a b c d : Nat) (ha : a < 17) (hb : b < 17) (hc : c < 17) (hd : d < 17)
    (o0 : a < b) (o1 : b < c) (o2 : c < d)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true) (p4 : e a d = true) (p5 : e b d = true) (p6 : e c d = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [o0, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [o1, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  have h4 := List.all_eq_true.mp h3 d (List.mem_range.mpr hd)
  simp only [o2, decide_true, Bool.not_true, p4, p5, p6, Bool.false_or] at h4
  exact Bool.noConfusion h4



/-! ## ⭐⭐ THE THREE FLOORS, LIFTED INTO THE CARRIER. Audit 8's finding closed. -/

theorem adj24_symm (x y : Nat) : adj24 x y = adj24 y x := by
  have hx : x % 24 < 24 := Nat.mod_lt _ (by decide)
  have hy : y % 24 < 24 := Nat.mod_lt _ (by decide)
  have h := List.all_eq_true.mp adj24_symm_res (x % 24) (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h (y % 24) (List.mem_range.mpr hy)
  simp only [beq_iff_eq] at h2
  simpa [adj24, Nat.mod_mod] using h2

theorem nadj24_symm (x y : Nat) : nadj24 x y = nadj24 y x := by
  unfold nadj24; rw [adj24_symm x y]

theorem gh_24_4 : gn_24_4 adj24 = true := by decide

theorem gh_24_5n : gn_24_5 nadj24 = true := by decide

theorem not_sufficesN_24 : ¬ SufficesN 24 4 5 := by
  intro hS
  have hlen : 24 ≤ (List.range 24).length := by simp
  rcases hS adj24 adj24_symm (List.range 24) List.nodup_range hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hind⟩
  · 
    obtain ⟨a, b, c, d, rfl⟩ := lenq4 hlk
    obtain ⟨q0, q1, q2⟩ := pwq4 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    exact gx_24_4 adj24 gh_24_4 a b c d
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp)) (hb d (by simp))
      q0 q1 q2
      (hcl a (by simp) b (by simp) (by omega)) (hcl a (by simp) c (by simp) (by omega)) (hcl b (by simp) c (by simp) (by omega)) (hcl a (by simp) d (by simp) (by omega)) (hcl b (by simp) d (by simp) (by omega)) (hcl c (by simp) d (by simp) (by omega))
  · 
    obtain ⟨a, b, c, d, f, rfl⟩ := lenq5 hlk
    obtain ⟨q0, q1, q2, q3⟩ := pwq5 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    have hn : ∀ x ∈ ([a, b, c, d, f] : List Nat), ∀ y ∈ ([a, b, c, d, f] : List Nat), x ≠ y → nadj24 x y = true := by
      intro x hx y hy hxy
      simp [nadj24, hind x hx y hy hxy]
    exact gx_24_5 nadj24 gh_24_5n a b c d f
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp)) (hb d (by simp)) (hb f (by simp))
      q0 q1 q2 q3
      (hn a (by simp) b (by simp) (by omega)) (hn a (by simp) c (by simp) (by omega)) (hn b (by simp) c (by simp) (by omega)) (hn a (by simp) d (by simp) (by omega)) (hn b (by simp) d (by simp) (by omega)) (hn c (by simp) d (by simp) (by omega)) (hn a (by simp) f (by simp) (by omega)) (hn b (by simp) f (by simp) (by omega)) (hn c (by simp) f (by simp) (by omega)) (hn d (by simp) f (by simp) (by omega))

theorem a35_symm (x y : Nat) : a35 x y = a35 y x := by
  have hx : x % 13 < 13 := Nat.mod_lt _ (by decide)
  have hy : y % 13 < 13 := Nat.mod_lt _ (by decide)
  have h := List.all_eq_true.mp a35_symm_res (x % 13) (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h (y % 13) (List.mem_range.mpr hy)
  simp only [beq_iff_eq] at h2
  simpa [a35, Nat.mod_mod] using h2

theorem n35_symm (x y : Nat) : n35 x y = n35 y x := by
  unfold n35; rw [a35_symm x y]

theorem gh_35_3 : gn_35_3 a35 = true := by decide

theorem gh_35_5n : gn_35_5 n35 = true := by decide

theorem not_sufficesN_35 : ¬ SufficesN 13 3 5 := by
  intro hS
  have hlen : 13 ≤ (List.range 13).length := by simp
  rcases hS a35 a35_symm (List.range 13) List.nodup_range hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hind⟩
  · 
    obtain ⟨a, b, c, rfl⟩ := lenq3 hlk
    obtain ⟨q0, q1⟩ := pwq3 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    exact gx_35_3 a35 gh_35_3 a b c
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp))
      q0 q1
      (hcl a (by simp) b (by simp) (by omega)) (hcl a (by simp) c (by simp) (by omega)) (hcl b (by simp) c (by simp) (by omega))
  · 
    obtain ⟨a, b, c, d, f, rfl⟩ := lenq5 hlk
    obtain ⟨q0, q1, q2, q3⟩ := pwq5 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    have hn : ∀ x ∈ ([a, b, c, d, f] : List Nat), ∀ y ∈ ([a, b, c, d, f] : List Nat), x ≠ y → n35 x y = true := by
      intro x hx y hy hxy
      simp [n35, hind x hx y hy hxy]
    exact gx_35_5 n35 gh_35_5n a b c d f
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp)) (hb d (by simp)) (hb f (by simp))
      q0 q1 q2 q3
      (hn a (by simp) b (by simp) (by omega)) (hn a (by simp) c (by simp) (by omega)) (hn b (by simp) c (by simp) (by omega)) (hn a (by simp) d (by simp) (by omega)) (hn b (by simp) d (by simp) (by omega)) (hn c (by simp) d (by simp) (by omega)) (hn a (by simp) f (by simp) (by omega)) (hn b (by simp) f (by simp) (by omega)) (hn c (by simp) f (by simp) (by omega)) (hn d (by simp) f (by simp) (by omega))

theorem a44_symm (x y : Nat) : a44 x y = a44 y x := by
  have hx : x % 17 < 17 := Nat.mod_lt _ (by decide)
  have hy : y % 17 < 17 := Nat.mod_lt _ (by decide)
  have h := List.all_eq_true.mp a44_symm_res (x % 17) (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h (y % 17) (List.mem_range.mpr hy)
  simp only [beq_iff_eq] at h2
  simpa [a44, Nat.mod_mod] using h2

theorem n44_symm (x y : Nat) : n44 x y = n44 y x := by
  unfold n44; rw [a44_symm x y]

theorem gh_44_4 : gn_44_4 a44 = true := by decide

theorem gh_44_4n : gn_44_4 n44 = true := by decide

theorem not_sufficesN_44 : ¬ SufficesN 17 4 4 := by
  intro hS
  have hlen : 17 ≤ (List.range 17).length := by simp
  rcases hS a44 a44_symm (List.range 17) List.nodup_range hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hind⟩
  · 
    obtain ⟨a, b, c, d, rfl⟩ := lenq4 hlk
    obtain ⟨q0, q1, q2⟩ := pwq4 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    exact gx_44_4 a44 gh_44_4 a b c d
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp)) (hb d (by simp))
      q0 q1 q2
      (hcl a (by simp) b (by simp) (by omega)) (hcl a (by simp) c (by simp) (by omega)) (hcl b (by simp) c (by simp) (by omega)) (hcl a (by simp) d (by simp) (by omega)) (hcl b (by simp) d (by simp) (by omega)) (hcl c (by simp) d (by simp) (by omega))
  · 
    obtain ⟨a, b, c, d, rfl⟩ := lenq4 hlk
    obtain ⟨q0, q1, q2⟩ := pwq4 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    have hn : ∀ x ∈ ([a, b, c, d] : List Nat), ∀ y ∈ ([a, b, c, d] : List Nat), x ≠ y → n44 x y = true := by
      intro x hx y hy hxy
      simp [n44, hind x hx y hy hxy]
    exact gx_44_4 n44 gh_44_4n a b c d
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp)) (hb d (by simp))
      q0 q1 q2
      (hn a (by simp) b (by simp) (by omega)) (hn a (by simp) c (by simp) (by omega)) (hn b (by simp) c (by simp) (by omega)) (hn a (by simp) d (by simp) (by omega)) (hn b (by simp) d (by simp) (by omega)) (hn c (by simp) d (by simp) (by omega))



/-! ## ⭐ NON-VACUITY CONTROLS ON THE NESTS THAT ACTUALLY CARRY THE MATHEMATICS.
    Audit 9's finding: the earlier controls were attached to the DESCENDING nests, while
    the carrier bridges use the ASCENDING `gn_*` nests. A control on the wrong object
    proves nothing about the right one. Each `gn_*` must be able to return FALSE. -/

theorem gnctrl_24_4 : gn_24_4 (fun _ _ => true) = false := by decide

theorem gnctrl_24_5 : gn_24_5 (fun _ _ => true) = false := by decide

theorem gnctrl_35_3 : gn_35_3 (fun _ _ => true) = false := by decide

theorem gnctrl_35_5 : gn_35_5 (fun _ _ => true) = false := by decide

theorem gnctrl_44_4 : gn_44_4 (fun _ _ => true) = false := by decide

/-- and the relations they are actually applied to, for the pairing to be visible -/
theorem gnpair_24 : gn_24_4 adj24 = true ∧ gn_24_5 nadj24 = true := ⟨gh_24_4, gh_24_5n⟩

theorem gnpair_35 : gn_35_3 a35 = true ∧ gn_35_5 n35 = true := ⟨gh_35_3, gh_35_5n⟩

theorem gnpair_44 : gn_44_4 a44 = true ∧ gn_44_4 n44 = true := ⟨gh_44_4, gh_44_4n⟩



/-! ## ⭐⭐ THE CHAIN AS NAMED THEOREMS, so its steps are results and not local `have`s,
    and then the two pairs this file PINS EXACTLY. -/

theorem ch11 : SufficesN 1 1 1 := suffices_one_leftN 1

theorem ch12 : SufficesN 1 1 2 := suffices_one_leftN 2

theorem ch13 : SufficesN 1 1 3 := suffices_one_leftN 3

theorem ch14 : SufficesN 1 1 4 := suffices_one_leftN 4

theorem ch15 : SufficesN 1 1 5 := suffices_one_leftN 5

theorem ch21 : SufficesN 1 2 1 := suffices_one_rightN 2

theorem ch22 : SufficesN 2 2 2 :=
  es_recurrenceN 1 1 2 2 (by omega) (by omega) (by omega) (by omega) ch12 ch21

theorem ch23 : SufficesN 3 2 3 :=
  es_recurrenceN 1 2 2 3 (by omega) (by omega) (by omega) (by omega) ch13 ch22

theorem ch24 : SufficesN 4 2 4 :=
  es_recurrenceN 1 3 2 4 (by omega) (by omega) (by omega) (by omega) ch14 ch23

theorem ch25 : SufficesN 5 2 5 :=
  es_recurrenceN 1 4 2 5 (by omega) (by omega) (by omega) (by omega) ch15 ch24

theorem ch31 : SufficesN 1 3 1 := suffices_one_rightN 3

theorem ch32 : SufficesN 3 3 2 :=
  es_recurrenceN 2 1 3 2 (by omega) (by omega) (by omega) (by omega) ch22 ch31

theorem ch33 : SufficesN 6 3 3 :=
  es_recurrenceN 3 3 3 3 (by omega) (by omega) (by omega) (by omega) ch23 ch32

theorem ch34 : SufficesN 9 3 4 :=
  gg_sharpening 4 6 3 4 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) ch24 ch33

theorem ch35 : SufficesN 14 3 5 :=
  es_recurrenceN 5 9 3 5 (by omega) (by omega) (by omega) (by omega) ch25 ch34

theorem ch41 : SufficesN 1 4 1 := suffices_one_rightN 4

theorem ch42 : SufficesN 4 4 2 :=
  es_recurrenceN 3 1 4 2 (by omega) (by omega) (by omega) (by omega) ch32 ch41

theorem ch43 : SufficesN 9 4 3 :=
  gg_sharpening 6 4 4 3 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) ch33 ch42

theorem ch44 : SufficesN 18 4 4 :=
  es_recurrenceN 9 9 4 4 (by omega) (by omega) (by omega) (by omega) ch34 ch43

theorem ch45 : SufficesN 31 4 5 :=
  gg_sharpening 14 18 4 5 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) ch35 ch44

theorem ch51 : SufficesN 1 5 1 := suffices_one_rightN 5

theorem ch52 : SufficesN 5 5 2 :=
  es_recurrenceN 4 1 5 2 (by omega) (by omega) (by omega) (by omega) ch42 ch51

theorem ch53 : SufficesN 14 5 3 :=
  es_recurrenceN 9 5 5 3 (by omega) (by omega) (by omega) (by omega) ch43 ch52

theorem ch54 : SufficesN 31 5 4 :=
  gg_sharpening 18 14 5 4 (by omega) (by omega) (by omega) (by omega) (by decide) (by decide) ch44 ch53

theorem ch55 : SufficesN 62 5 5 :=
  es_recurrenceN 31 31 5 5 (by omega) (by omega) (by omega) (by omega) ch45 ch54

/-- ⭐ R(3,5) = 14, EXACTLY, floor and ceiling both in the carrier, in this file. -/
theorem R35_exact : IsExactlyN 14 3 5 := ⟨ch35, not_sufficesN_35⟩

/-- ⭐ R(4,4) = 18, EXACTLY, floor and ceiling both in the carrier, in this file. -/
theorem R44_exact : IsExactlyN 18 4 4 := ⟨ch44, not_sufficesN_44⟩

/-- and the four-five pair, where the campaign has a proved six-wide slack and no exact value -/
theorem R45_bracket (N : Nat) (hN : IsExactlyN N 4 5) : 25 ≤ N ∧ N ≤ 31 := by
  have hnot := hN.2
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge N 25 with hlt | hge
    · exact absurd (sufficesN_mono N 24 4 5 (by omega) hN.1) not_sufficesN_24
    · exact hge
  · rcases Nat.lt_or_ge 31 N with hgt | hle
    · exact absurd (sufficesN_mono 31 (N - 1) 4 5 (by omega) ch45) hnot
    · exact hle



/-! ## ⭐⭐ TWO MORE SETTLED PAIRS ON THE SAME CARRIER, to make the method's reach
    measurable rather than asserted: R(3,3) and R(3,4). -/

def S33 : List Nat := [1, 4]

def a33 (i j : Nat) : Bool := S33.contains ((i % 5 + 5 - j % 5) % 5)

def n33 (i j : Nat) : Bool := ! a33 i j

theorem a33_symm_res :
    (List.range 5).all (fun i => (List.range 5).all (fun j => a33 i j == a33 j i)) = true := by decide

theorem a33_symm (x y : Nat) : a33 x y = a33 y x := by
  have hx : x % 5 < 5 := Nat.mod_lt _ (by decide)
  have hy : y % 5 < 5 := Nat.mod_lt _ (by decide)
  have h := List.all_eq_true.mp a33_symm_res (x % 5) (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h (y % 5) (List.mem_range.mpr hy)
  simp only [beq_iff_eq] at h2
  simpa [a33, Nat.mod_mod] using h2

def gn_33_3 (e : Nat → Nat → Bool) : Bool :=
  (List.range 5).all fun a => (List.range 5).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 5).all fun c => (! (b < c)) || (! e a c) || (! e b c))

theorem gx_33_3 (e : Nat → Nat → Bool) (h : gn_33_3 e = true)
    (a b c : Nat) (ha : a < 5) (hb : b < 5) (hc : c < 5)
    (o0 : a < b) (o1 : b < c)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [o0, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [o1, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  exact Bool.noConfusion h3

theorem gh_33_3 : gn_33_3 a33 = true := by decide

theorem gh_33_3n : gn_33_3 n33 = true := by decide

theorem gnctrl_33_3 : gn_33_3 (fun _ _ => true) = false := by decide

theorem not_sufficesN_33 : ¬ SufficesN 5 3 3 := by
  intro hS
  have hlen : 5 ≤ (List.range 5).length := by simp
  rcases hS a33 a33_symm (List.range 5) List.nodup_range hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hind⟩
  · 
    obtain ⟨a, b, c, rfl⟩ := lenq3 hlk
    obtain ⟨q0, q1⟩ := pwq3 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    exact gx_33_3 a33 gh_33_3 a b c
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp))
      q0 q1
      (hcl a (by simp) b (by simp) (by omega)) (hcl a (by simp) c (by simp) (by omega)) (hcl b (by simp) c (by simp) (by omega))
  · 
    obtain ⟨a, b, c, rfl⟩ := lenq3 hlk
    obtain ⟨q0, q1⟩ := pwq3 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    have hn : ∀ x ∈ ([a, b, c] : List Nat), ∀ y ∈ ([a, b, c] : List Nat), x ≠ y → n33 x y = true := by
      intro x hx y hy hxy
      simp [n33, hind x hx y hy hxy]
    exact gx_33_3 n33 gh_33_3n a b c
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp))
      q0 q1
      (hn a (by simp) b (by simp) (by omega)) (hn a (by simp) c (by simp) (by omega)) (hn b (by simp) c (by simp) (by omega))

def S34 : List Nat := [1, 4, 7]

def a34 (i j : Nat) : Bool := S34.contains ((i % 8 + 8 - j % 8) % 8)

def n34 (i j : Nat) : Bool := ! a34 i j

theorem a34_symm_res :
    (List.range 8).all (fun i => (List.range 8).all (fun j => a34 i j == a34 j i)) = true := by decide

theorem a34_symm (x y : Nat) : a34 x y = a34 y x := by
  have hx : x % 8 < 8 := Nat.mod_lt _ (by decide)
  have hy : y % 8 < 8 := Nat.mod_lt _ (by decide)
  have h := List.all_eq_true.mp a34_symm_res (x % 8) (List.mem_range.mpr hx)
  have h2 := List.all_eq_true.mp h (y % 8) (List.mem_range.mpr hy)
  simp only [beq_iff_eq] at h2
  simpa [a34, Nat.mod_mod] using h2

def gn_34_3 (e : Nat → Nat → Bool) : Bool :=
  (List.range 8).all fun a => (List.range 8).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 8).all fun c => (! (b < c)) || (! e a c) || (! e b c))

theorem gx_34_3 (e : Nat → Nat → Bool) (h : gn_34_3 e = true)
    (a b c : Nat) (ha : a < 8) (hb : b < 8) (hc : c < 8)
    (o0 : a < b) (o1 : b < c)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [o0, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [o1, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  exact Bool.noConfusion h3

def gn_34_4 (e : Nat → Nat → Bool) : Bool :=
  (List.range 8).all fun a => (List.range 8).all fun b => (! (a < b)) || (! e a b) ||
      ((List.range 8).all fun c => (! (b < c)) || (! e a c) || (! e b c) ||
      ((List.range 8).all fun d => (! (c < d)) || (! e a d) || (! e b d) || (! e c d)))

theorem gx_34_4 (e : Nat → Nat → Bool) (h : gn_34_4 e = true)
    (a b c d : Nat) (ha : a < 8) (hb : b < 8) (hc : c < 8) (hd : d < 8)
    (o0 : a < b) (o1 : b < c) (o2 : c < d)
    (p1 : e a b = true) (p2 : e a c = true) (p3 : e b c = true) (p4 : e a d = true) (p5 : e b d = true) (p6 : e c d = true) :
    False := by
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [o0, decide_true, Bool.not_true, p1, Bool.false_or] at h2
  have h3 := List.all_eq_true.mp h2 c (List.mem_range.mpr hc)
  simp only [o1, decide_true, Bool.not_true, p2, p3, Bool.false_or] at h3
  have h4 := List.all_eq_true.mp h3 d (List.mem_range.mpr hd)
  simp only [o2, decide_true, Bool.not_true, p4, p5, p6, Bool.false_or] at h4
  exact Bool.noConfusion h4

theorem gh_34_3 : gn_34_3 a34 = true := by decide

theorem gh_34_4n : gn_34_4 n34 = true := by decide

theorem gnctrl_34_3 : gn_34_3 (fun _ _ => true) = false := by decide

theorem not_sufficesN_34 : ¬ SufficesN 8 3 4 := by
  intro hS
  have hlen : 8 ≤ (List.range 8).length := by simp
  rcases hS a34 a34_symm (List.range 8) List.nodup_range hlen with ⟨K, hsub, hlk, hcl⟩ | ⟨K, hsub, hlk, hind⟩
  · 
    obtain ⟨a, b, c, rfl⟩ := lenq3 hlk
    obtain ⟨q0, q1⟩ := pwq3 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    exact gx_34_3 a34 gh_34_3 a b c
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp))
      q0 q1
      (hcl a (by simp) b (by simp) (by omega)) (hcl a (by simp) c (by simp) (by omega)) (hcl b (by simp) c (by simp) (by omega))
  · 
    obtain ⟨a, b, c, d, rfl⟩ := lenq4 hlk
    obtain ⟨q0, q1, q2⟩ := pwq4 (sub_range_pairwise hsub)
    have hb := sub_range_lt hsub
    have hn : ∀ x ∈ ([a, b, c, d] : List Nat), ∀ y ∈ ([a, b, c, d] : List Nat), x ≠ y → n34 x y = true := by
      intro x hx y hy hxy
      simp [n34, hind x hx y hy hxy]
    exact gx_34_4 n34 gh_34_4n a b c d
      (hb a (by simp)) (hb b (by simp)) (hb c (by simp)) (hb d (by simp))
      q0 q1 q2
      (hn a (by simp) b (by simp) (by omega)) (hn a (by simp) c (by simp) (by omega)) (hn b (by simp) c (by simp) (by omega)) (hn a (by simp) d (by simp) (by omega)) (hn b (by simp) d (by simp) (by omega)) (hn c (by simp) d (by simp) (by omega))

/-- audit 10's finding: the control generator emitted one control per block, keyed on the
    CLIQUE size, so a block whose two nests differ in depth left the second uncontrolled.
    gn_34_4 is that nest. -/
theorem gnctrl_34_4 : gn_34_4 (fun _ _ => true) = false := by decide

theorem R33_exact : IsExactlyN 6 3 3 := ⟨ch33, not_sufficesN_33⟩

theorem R34_exact : IsExactlyN 9 3 4 := ⟨ch34, not_sufficesN_34⟩

/-! ## ⭐⭐⭐ THE WHOLE CAMPAIGN, AS ONE CHECKABLE STATEMENT.
    Check this declaration's statement and its axioms and you have checked everything the
    artefact claims. Nothing here depends on the file's single sorry. -/

theorem R55_CAMPAIGN :
    IsExactlyN 6 3 3 ∧ IsExactlyN 9 3 4 ∧ IsExactlyN 14 3 5 ∧ IsExactlyN 18 4 4 ∧
    (∀ N, IsExactlyN N 4 5 → 25 ≤ N ∧ N ≤ 31) ∧
    (∀ N, IsExactlyN N 5 5 → 42 ≤ N ∧ N ≤ 62) :=
  ⟨R33_exact, R34_exact, R35_exact, R44_exact, R45_bracket, exact_value_in_bracket62⟩

/-- and the open obligation stated beside it: closing this pins the last line to two orders -/
theorem R55_OPEN : SufficesN 43 5 5 → ∀ N, IsExactlyN N 5 5 → N = 42 ∨ N = 43 :=
  leverage_43

theorem msl_r55_campaign_summary_v2  : (62 : Nat) - 42 = 20 := by decide
