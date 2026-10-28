import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData
import OAI.AlgebraicGeometry.GroupSchemes.FiniteEtale
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic

/-! # Blocks Projectors -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

noncomputable section

section

/-!
Finite-level blocks are subfunctors of the actual abelian torsion functor,
tested on every scheme, including nonreduced schemes. The q-divisibility
and height predicate asks for a compatible representation by FiniteEtale's actual
finite group schemes. It does not prescribe the height by definition.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

variable {O : Type} [CommRing O] {S : Scheme} {g q : ℕ} [Fact q.Prime]

/-- The χ-block of A[q^n], expressed by its actual integral endomorphism action. -/
def blockPoints (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
    (χ : O →+* PadicInt q) (n : ℕ) (T : Over S) : Subgroup (T ⟶ A.scheme) where
  carrier := {x | x ^ (q ^ n) = 1 ∧
    ∀ a : O, x ≫ ρ.map a = x ^ (PadicInt.toZModPow n (χ a)).val}
  one_mem' := by simp [MonObj.one_comp]
  mul_mem' := by
    intro x y hx hy
    constructor
    · rw [mul_pow, hx.1, hy.1, one_mul]
    · intro a
      rw [MonObj.mul_comp, hx.2 a, hy.2 a, mul_pow]
  inv_mem' := by
    intro x hx
    constructor
    · rw [inv_pow, hx.1, inv_one]
    · intro a
      rw [GrpObj.inv_comp, hx.2 a, inv_pow]

def blockPullback (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
    (χ : O →+* PadicInt q) (n : ℕ) {T U : Over S} (f : T ⟶ U) :
    blockPoints A ρ χ n U →* blockPoints A ρ χ n T where
  toFun x := ⟨f ≫ x.val, by
    constructor
    · rw [← MonObj.comp_pow, x.property.1, MonObj.comp_one]
    · intro a
      rw [Category.assoc, x.property.2 a, MonObj.comp_pow]⟩
  map_one' := Subtype.ext (MonObj.comp_one f)
  map_mul' x y := Subtype.ext (MonObj.comp_mul f x.val y.val)

def blockFunctor (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
    (χ : O →+* PadicInt q) (n : ℕ) : (Over S)ᵒᵖ ⥤ GrpCat where
  obj T := GrpCat.of (blockPoints A ρ χ n T.unop)
  map f := GrpCat.ofHom (blockPullback A ρ χ n f.unop)
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.id_comp x.val)
  map_comp f h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact Subtype.ext (Category.assoc _ _ x.val)

def blockInclusion (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
    (χ : O →+* PadicInt q) (n : ℕ) : blockFunctor A ρ χ n ⟶ A.torsionFunctor (q ^ n) where
  app _T := GrpCat.ofHom {
    toFun x := ⟨x.val, x.property.1⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  naturality _ _ _ := rfl

variable {k : Type} [Field k]

/-- Restriction to affine test algebras, in exactly FiniteEtale's convention. -/
def affineBlockFunctor (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (χ : O →+* PadicInt q) (n : ℕ) :
    CommAlgCat k ⥤ GrpCat where
  obj R := GrpCat.of (blockPoints A ρ χ n (GroupSchemes.FiniteEtale.affine k R))
  map f := GrpCat.ofHom (blockPullback A ρ χ n
    ((algSpec (CommRingCat.of k)).map f.op))
  map_id R := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (algSpec (.of k)).map (𝟙 R).op ≫ x.val = x.val
    simp
  map_comp f h := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    change (algSpec (.of k)).map (f ≫ h).op ≫ x.val = _
    simp [blockPullback, Category.assoc]

/-- Height h means compatible representation by a genuine q-divisible
group of height h. No classification or height-three assertion is a field
of the PEL model or the integral reduction. -/
def BlockHasHeight (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A) (χ : O →+* PadicInt q) (h : ℕ) : Prop :=
  ∃ G : GroupSchemes.FiniteEtale.PDivisibleGroup k q h,
    ∃ e : ∀ n : ℕ,
      (G.level n).points ⋙ forget₂ CommGrpCat GrpCat ≅ affineBlockFunctor A ρ χ n,
      ∀ (n : ℕ) (R : CommAlgCat k) (x : GroupSchemes.FiniteEtale.affine k R ⟶ (G.level n).scheme),
        (((e (n + 1)).hom.app R) (x ≫ G.inclusion n)).val =
          (((e n).hom.app R) x).val

end

section

/-! Actual finite-level block schemes, obtained by two scheme equalizers.
The first equation is q^n torsion and the second fixes an integral lift of
the split coefficient idempotent. Neither reducedness nor ordinarity is
required for these constructions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {S : Scheme} {g : ℕ} {O : Type} [CommRing O]
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)

abbrev torsionScheme (m : ℕ) : Over S := equalizer ((𝟙 A.scheme) ^ m) (1 : A.scheme ⟶ A.scheme)

abbrev torsionInclusion (m : ℕ) : torsionScheme A m ⟶ A.scheme :=
  equalizer.ι ((𝟙 A.scheme) ^ m) (1 : A.scheme ⟶ A.scheme)

def torsionPointsEquiv (m : ℕ) (T : Over S) :
    (T ⟶ torsionScheme A m) ≃ {x : T ⟶ A.scheme // x ^ m = 1} where
  toFun f := ⟨f ≫ torsionInclusion A m, by
    have hm : (torsionInclusion A m) ^ m = 1 := by
      simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using
        (equalizer.condition ((𝟙 A.scheme) ^ m) (1 : A.scheme ⟶ A.scheme))
    rw [← MonObj.comp_pow, hm, MonObj.comp_one]⟩
  invFun x := equalizer.lift x.val (by
    simpa only [MonObj.comp_pow, Category.comp_id, MonObj.comp_one] using x.prop)
  left_inv f := by apply equalizer.hom_ext; exact equalizer.lift_ι _ _
  right_inv x := by apply Subtype.ext; exact equalizer.lift_ι _ _

/-- The scheme cut out by [m]x=0 and ex=x. -/
abbrev idempotentBlockScheme (m : ℕ) (e : O) : Over S :=
  equalizer (torsionInclusion A m ≫ ρ.map e) (torsionInclusion A m)

abbrev idempotentBlockInclusion (m : ℕ) (e : O) :
    idempotentBlockScheme A ρ m e ⟶ A.scheme :=
  equalizer.ι (torsionInclusion A m ≫ ρ.map e) (torsionInclusion A m) ≫ torsionInclusion A m

def idempotentBlockPointsEquiv (m : ℕ) (e : O) (T : Over S) :
    (T ⟶ idempotentBlockScheme A ρ m e) ≃
      {x : T ⟶ A.scheme // x ^ m = 1 ∧ x ≫ ρ.map e = x} where
  toFun f := ⟨f ≫ idempotentBlockInclusion A ρ m e, by
    constructor
    · exact (torsionPointsEquiv A m T (f ≫ equalizer.ι _ _)).property
    · simpa only [idempotentBlockInclusion, Category.assoc] using
        congrArg (fun z => f ≫ z)
          (equalizer.condition (torsionInclusion A m ≫ ρ.map e) (torsionInclusion A m))⟩
  invFun x := equalizer.lift ((torsionPointsEquiv A m T).symm ⟨x.val, x.property.1⟩) (by
    change (equalizer.lift x.val _) ≫ (torsionInclusion A m ≫ ρ.map e) =
      (equalizer.lift x.val _) ≫ torsionInclusion A m
    rw [← Category.assoc]
    simp only [torsionInclusion, equalizer.lift_ι]
    exact x.property.2)
  left_inv f := by
    apply equalizer.hom_ext
    rw [equalizer.lift_ι]
    apply equalizer.hom_ext
    change equalizer.lift (f ≫ idempotentBlockInclusion A ρ m e) _ ≫
      torsionInclusion A m = _
    rw [equalizer.lift_ι]
    exact (Category.assoc _ _ _).symm
  right_inv x := by
    apply Subtype.ext
    dsimp only [idempotentBlockInclusion]
    rw [← Category.assoc, equalizer.lift_ι]
    exact congrArg Subtype.val ((torsionPointsEquiv A m T).apply_symm_apply ⟨x.val, x.property.1⟩)

instance idempotentBlockInclusion_closed (m : ℕ) (e : O) :
    IsClosedImmersion (idempotentBlockInclusion A ρ m e).left := by
  have ht : IsClosedImmersion (torsionInclusion A m).left :=
    isClosedImmersion_equalizer_ι_left _ _
  have hb : IsClosedImmersion
      (equalizer.ι (torsionInclusion A m ≫ ρ.map e) (torsionInclusion A m)).left :=
    isClosedImmersion_equalizer_ι_left _ _
  change IsClosedImmersion
    ((equalizer.ι (torsionInclusion A m ≫ ρ.map e) (torsionInclusion A m)).left ≫
      (torsionInclusion A m).left)
  infer_instance

theorem integralAction_natCast (n : ℕ) : ρ.map (n : O) = (𝟙 A.scheme) ^ n := by
  induction n with
  | zero => simpa using ρ.map_zero
  | succ n ih =>
      rw [Nat.cast_succ, ρ.map_add, ρ.map_one, ih, pow_succ]

/-- Integral endomorphisms congruent modulo m agree on all m-torsion points. -/
theorem action_eq_of_congruence (b c : O) (m : ℕ)
    (hbc : b - c ∈ Ideal.span ({(m : O)} : Set O))
    (T : Over S) (x : T ⟶ A.scheme) (hx : x ^ m = 1) :
    x ≫ ρ.map b = x ≫ ρ.map c := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hbc
  have hb : b = c + r * (m : O) := by
    rw [mul_comm r, ← hr]
    abel
  rw [hb, ρ.map_add, MonObj.comp_mul, ρ.map_mul, integralAction_natCast,
    ← Category.assoc, MonObj.comp_pow, Category.comp_id, hx,
    MonObj.one_comp, mul_one]

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K)
  (hsplit : j.HasSplitCoordinates iota)
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)

/-- The character definition of a block equals the fixed space of the
actual split residue idempotent, on every test scheme. -/
theorem mem_block_iff_fixed (n : ℕ) (τ : Gal(E/ℚ))
    (T : Over S) (x : T ⟶ B.scheme) :
    x ∈ blockPoints B σ (j.localCharacter iota τ) n T ↔
      x ^ (q ^ n) = 1 ∧ x ≫ σ.map (j.projector iota hsplit n τ) = x := by
  classical
  let : NeZero (q ^ n) := ⟨pow_ne_zero _ (Fact.out : q.Prime).ne_zero⟩
  let e := j.projector iota hsplit n τ
  have he := j.projector_coordinates iota hsplit n τ
  change j.residueCoordinates iota n e = Pi.single τ 1 at he
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have heτ := congrFun he τ
    change PadicInt.toZModPow n (j.localCharacter iota τ e) = _ at heτ
    simp only [Pi.single_eq_same] at heτ
    rw [hx.2 e, heτ]
    have hmod : (1 : ZMod (q ^ n)).val = 1 % (q ^ n) :=
      by simpa using ZMod.val_natCast (q ^ n) 1
    rw [hmod]
    exact (pow_eq_pow_of_modEq (show 1 % (q ^ n) ≡ 1 [MOD q ^ n] by
      change (1 % (q ^ n)) % (q ^ n) = 1 % (q ^ n)
      rw [Nat.mod_mod]) hx.1).trans (pow_one x)
  · rintro ⟨hx, hxe⟩
    refine ⟨hx, ?_⟩
    intro a
    let k := (j.residueCharacter iota τ n a).val
    have hr : j.residueCoordinates iota n (a * e) =
        j.residueCoordinates iota n ((k : NumberField.RingOfIntegers E) * e) := by
      rw [map_mul, map_mul, map_natCast, he]
      ext υ
      change j.residueCharacter iota υ n a * (Pi.single τ 1 : Gal(E/ℚ) → ZMod (q ^ n)) υ =
        (k : ZMod (q ^ n)) * (Pi.single τ 1 : Gal(E/ℚ) → ZMod (q ^ n)) υ
      by_cases hv : υ = τ
      · subst υ
        simp only [Pi.single_eq_same, mul_one]
        exact (ZMod.natCast_zmod_val (j.residueCharacter iota τ n a)).symm
      · simp [hv]
    have hc : a * e - (k : NumberField.RingOfIntegers E) * e ∈
        Ideal.span ({(q ^ n : NumberField.RingOfIntegers E)} :
          Set (NumberField.RingOfIntegers E)) := by
      rw [← (hsplit n).2]
      change j.residueCoordinates iota n (a * e - (k : NumberField.RingOfIntegers E) * e) = 0
      rw [map_sub, hr, sub_self]
    have hh := action_eq_of_congruence B σ _ _ (q ^ n)
      (by simpa only [Nat.cast_pow] using hc) T x hx
    rw [σ.map_mul, σ.map_mul, ← Category.assoc, ← Category.assoc, hxe,
      integralAction_natCast, MonObj.comp_pow, Category.comp_id] at hh
    exact hh

/-- The constructed block scheme represents the character-defined block
on every test scheme; the equivalence retains infinitesimal points. -/
def splitBlockSchemePointsEquiv (n : ℕ) (τ : Gal(E/ℚ)) (T : Over S) :
    (T ⟶ idempotentBlockScheme B σ (q ^ n) (j.projector iota hsplit n τ)) ≃
      blockPoints B σ (j.localCharacter iota τ) n T :=
  (idempotentBlockPointsEquiv B σ (q ^ n) (j.projector iota hsplit n τ) T).trans
    (Equiv.subtypeEquivRight (fun x => (mem_block_iff_fixed j iota hsplit B σ n τ T x).symm))

def splitBlockRepresentable (n : ℕ) (τ : Gal(E/ℚ)) :
    (blockFunctor B σ (j.localCharacter iota τ) n ⋙ forget GrpCat).RepresentableBy
      (idempotentBlockScheme B σ (q ^ n) (j.projector iota hsplit n τ)) where
  homEquiv := splitBlockSchemePointsEquiv j iota hsplit B σ n τ _
  homEquiv_comp f a := Subtype.ext (Category.assoc f a _)

/-- The group law on the actual equalizer scheme is recovered from its
represented block functor; it is not postulated as a model field. -/
def splitBlockGroupScheme (n : ℕ) (τ : Gal(E/ℚ)) : CommGrp (Over S) := by
  let X := idempotentBlockScheme B σ (q ^ n) (j.projector iota hsplit n τ)
  let F := blockFunctor B σ (j.localCharacter iota τ) n
  let rep := splitBlockRepresentable j iota hsplit B σ n τ
  letI : GrpObj X := GrpObj.ofRepresentableBy X F rep
  let e := yonedaGrpObjIsoOfRepresentableBy X F rep
  have hcomm : IsCommMonObj X := by
    apply (isCommMonObj_iff_isMulCommutative X).mpr
    intro T
    let : CommGroup (F.obj (.op T)) :=
      inferInstanceAs (CommGroup (blockPoints B σ (j.localCharacter iota τ) n T))
    refine ⟨⟨fun a b => ?_⟩⟩
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app (.op T))).1
    change (e.hom.app (.op T)) (a * b) = (e.hom.app (.op T)) (b * a)
    exact ((e.hom.app (.op T)).hom.map_mul a b).trans
      ((mul_comm _ _).trans ((e.hom.app (.op T)).hom.map_mul b a).symm)
  exact { X := X, grp := inferInstance, comm := hcomm }

end

/-! Character blocks commute with actual base change. The comparison
uses the abelian-scheme point adjunction and preserves the coefficient
action on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj

def representableByRightAdjoint
    {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {F : Dᵒᵖ ⥤ Type*} {X : D} (rep : F.RepresentableBy X) :
    (L.op ⋙ F).RepresentableBy (R.obj X) where
  homEquiv := (adj.homEquiv _ X).symm.trans rep.homEquiv
  homEquiv_comp f g := by
    change rep.homEquiv ((adj.homEquiv _ X).symm (f ≫ g)) = _
    rw [adj.homEquiv_naturality_left_symm, rep.homEquiv_comp]
    rfl

variable {O : Type} [CommRing O] {S S' : Scheme} {g q : ℕ} [Fact q.Prime]
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction O A)
  (f : S' ⟶ S) (χ : O →+* PadicInt q) (n : ℕ)

theorem baseChangePoints_action (T : Over S') (a : O) (x : (A.pullback f).Points T) :
    A.baseChangePointsMulEquiv f T (x ≫ (ρ.pullback f).map a) =
      A.baseChangePointsMulEquiv f T x ≫ ρ.map a := by
  apply Over.OverMorphism.ext
  change (x.left ≫ ((Over.pullback f).map (ρ.map a)).left) ≫
      CategoryTheory.Limits.pullback.fst A.scheme.hom f =
    (x.left ≫ CategoryTheory.Limits.pullback.fst A.scheme.hom f) ≫ (ρ.map a).left
  calc
    _ = x.left ≫ (((Over.pullback f).map (ρ.map a)).left ≫
        CategoryTheory.Limits.pullback.fst A.scheme.hom f) := Category.assoc _ _ _
    _ = x.left ≫ (CategoryTheory.Limits.pullback.fst A.scheme.hom f ≫ (ρ.map a).left) :=
      congrArg (fun z => x.left ≫ z) (CategoryTheory.Limits.pullback.lift_fst _ _ _)
    _ = _ := (Category.assoc _ _ _).symm

theorem baseChangePoints_mem_block (T : Over S') (x : (A.pullback f).Points T) :
    x ∈ blockPoints (A.pullback f) (ρ.pullback f) χ n T ↔
      A.baseChangePointsMulEquiv f T x ∈ blockPoints A ρ χ n ((Over.map f).obj T) := by
  let e := A.baseChangePointsMulEquiv f T
  constructor
  · intro hx
    refine ⟨?_, fun a => ?_⟩
    · exact (map_pow e x _).symm.trans ((congrArg e hx.1).trans e.map_one)
    · exact (baseChangePoints_action A ρ f T a x).symm.trans
        ((congrArg e (hx.2 a)).trans (map_pow e x _))
  · intro hx
    refine ⟨?_, fun a => ?_⟩
    · apply e.injective
      exact (map_pow e x _).trans (hx.1.trans e.map_one.symm)
    · apply e.injective
      exact (baseChangePoints_action A ρ f T a x).trans
        ((hx.2 a).trans (map_pow e x _).symm)

def blockBaseChangeEquiv (T : Over S') :
    blockPoints (A.pullback f) (ρ.pullback f) χ n T ≃*
      blockPoints A ρ χ n ((Over.map f).obj T) where
  toEquiv := (A.baseChangePointsMulEquiv f T).toEquiv.subtypeEquiv
    (baseChangePoints_mem_block A ρ f χ n T)
  map_mul' x y := Subtype.ext ((A.baseChangePointsMulEquiv f T).map_mul x.val y.val)

def blockBaseChangeIso :
    blockFunctor (A.pullback f) (ρ.pullback f) χ n ≅ (Over.map f).op ⋙ blockFunctor A ρ χ n :=
  NatIso.ofComponents (fun T => MulEquiv.toGrpIso (blockBaseChangeEquiv A ρ f χ n T.unop)) (by
    intro T U h
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact Category.assoc _ _ _)

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ}
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)

def splitBlockBaseChangeRepresentable (τ : Gal(E/ℚ)) :
    (blockFunctor (B.pullback f) (σ.pullback f) (j.localCharacter iota τ) n ⋙ forget GrpCat).RepresentableBy
      ((Over.pullback f).obj (idempotentBlockScheme B σ (q ^ n) (j.projector iota hsplit n τ))) := by
  let rep := representableByRightAdjoint (Over.mapPullbackAdj f)
    (splitBlockRepresentable j iota hsplit B σ n τ)
  let e := Functor.isoWhiskerRight (blockBaseChangeIso B σ f (j.localCharacter iota τ) n) (forget GrpCat)
  exact rep.ofIso e.symm

def splitBlockBaseChangeIso (τ : Gal(E/ℚ)) :
    (Over.pullback f).obj (idempotentBlockScheme B σ (q ^ n) (j.projector iota hsplit n τ)) ≅
      idempotentBlockScheme (B.pullback f) (σ.pullback f) (q ^ n) (j.projector iota hsplit n τ) :=
  (splitBlockBaseChangeRepresentable f n j iota hsplit B σ τ).uniqueUpToIso
    (splitBlockRepresentable j iota hsplit (B.pullback f) (σ.pullback f) n τ)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors
