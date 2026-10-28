import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELQuotientBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.IsogenyNaturality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PEL.Classifying
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # PEL Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELFunctor

noncomputable section

section

/-! Isomorphisms of paired PEL quotients preserve the actual source
and target PEL families and the forward isogeny. The reverse square
is a consequence, so the swap acts on their isomorphism classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T U : Over (Spec (.of K))}
    {A B A' B' A'' B'' : PEL.Objects.PELObject P iota N T}

structure PairedPELQuotientIso (f : PELQuotients.PairedPELQuotient A B n)
    (g : PELQuotients.PairedPELQuotient A' B' n) where
  source : PEL.Objects.PELIso A A'
  target : PEL.Objects.PELIso B B'
  forward_square : f.forward.isogeny.hom ≫ target.polarized.abelian.hom =
    source.polarized.abelian.hom ≫ g.forward.isogeny.hom

namespace PairedPELQuotientIso

variable {f : PELQuotients.PairedPELQuotient A B n} {g : PELQuotients.PairedPELQuotient A' B' n}
    {h : PELQuotients.PairedPELQuotient A'' B'' n}

def refl (f : PELQuotients.PairedPELQuotient A B n) : PairedPELQuotientIso f f where
  source := PEL.Objects.PELIso.refl A
  target := PEL.Objects.PELIso.refl B
  forward_square := by simp [PEL.Objects.PELIso.refl, HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl]

def symm (e : PairedPELQuotientIso f g) : PairedPELQuotientIso g f where
  source := e.source.symm
  target := e.target.symm
  forward_square := by
    change g.forward.isogeny.hom ≫ e.target.polarized.abelian.inv =
      e.source.polarized.abelian.inv ≫ f.forward.isogeny.hom
    apply (cancel_epi e.source.polarized.abelian.hom).mp
    rw [← Category.assoc, ← e.forward_square, Category.assoc,
      e.target.polarized.abelian.hom_inv_id, Category.comp_id,
      ← Category.assoc, e.source.polarized.abelian.hom_inv_id, Category.id_comp]

def trans (e : PairedPELQuotientIso f g) (d : PairedPELQuotientIso g h) :
    PairedPELQuotientIso f h where
  source := e.source.trans d.source
  target := e.target.trans d.target
  forward_square := by
    change f.forward.isogeny.hom ≫
        (e.target.polarized.abelian.hom ≫ d.target.polarized.abelian.hom) =
      (e.source.polarized.abelian.hom ≫ d.source.polarized.abelian.hom) ≫ h.forward.isogeny.hom
    rw [← Category.assoc, e.forward_square, Category.assoc, d.forward_square, Category.assoc]

theorem reverse_square (e : PairedPELQuotientIso f g) :
    f.reverse.isogeny.hom ≫ e.source.polarized.abelian.hom =
      e.target.polarized.abelian.hom ≫ g.reverse.isogeny.hom := by
  let : EffectiveEpi f.forward.isogeny.hom :=
    PELModuli.IntegralModel.IsogenyFactorizationIs.IsogenyFactorization.effectiveEpi_over_of_fpqc f.forward.isogeny.hom
  exact IsogenyNaturality.paired_isogeny_reverse_naturality f.forward.isogeny.hom f.reverse.isogeny.hom
    g.forward.isogeny.hom g.reverse.isogeny.hom
    e.source.polarized.abelian.hom e.target.polarized.abelian.hom n
    f.forward_reverse g.forward_reverse e.forward_square

def swap (e : PairedPELQuotientIso f g) : PairedPELQuotientIso f.swap g.swap where
  source := e.target
  target := e.source
  forward_square := e.reverse_square

def pullback (e : PairedPELQuotientIso f g) (b : U ⟶ T) :
    PairedPELQuotientIso (f.pullback b) (g.pullback b) where
  source := e.source.pullback b
  target := e.target.pullback b
  forward_square := ((Over.pullback b.left).map_comp _ _).symm.trans
    ((congrArg ((Over.pullback b.left).map) e.forward_square).trans
      ((Over.pullback b.left).map_comp _ _))

end PairedPELQuotientIso

end

/-! The paired-isogeny moduli functor has actual PEL families as its
objects and complete PEL isomorphisms as its equivalence relation.
Its two forgetful maps and swap are natural on all test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    {T U V : Over (Spec (.of K))}

structure PairedPELObject (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (N n : ℕ) (T : Over (Spec (.of K))) where
  source : PEL.Objects.PELObject P iota N T
  target : PEL.Objects.PELObject P iota N T
  quotient : PELQuotients.PairedPELQuotient source target n

def PairedPELObject.swap (A : PairedPELObject P iota N n T) : PairedPELObject P iota N n T where
  source := A.target
  target := A.source
  quotient := A.quotient.swap

theorem PairedPELObject.swap_swap (A : PairedPELObject P iota N n T) : A.swap.swap = A := rfl

def PairedPELObject.pullback (A : PairedPELObject P iota N n T) (f : U ⟶ T) :
    PairedPELObject P iota N n U where
  source := A.source.pullback f
  target := A.target.pullback f
  quotient := A.quotient.pullback f

def PairedPELObject.pullbackIdIso (A : PairedPELObject P iota N n T) :
    PairedPELQuotientIso (A.pullback (𝟙 T)).quotient A.quotient where
  source := PEL.Objects.PELIso.pullbackId A.source
  target := PEL.Objects.PELIso.pullbackId A.target
  forward_square := by
    change (Over.pullback (𝟙 T.left)).map A.quotient.forward.isogeny.hom ≫
        A.target.polarized.abelian.pullbackIdIso.hom =
      A.source.polarized.abelian.pullbackIdIso.hom ≫ A.quotient.forward.isogeny.hom
    rw [HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom, HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackIdIso_hom]
    exact Over.pullbackId.hom.naturality A.quotient.forward.isogeny.hom

def PairedPELObject.pullbackCompIso (A : PairedPELObject P iota N n T)
    (f : U ⟶ T) (h : V ⟶ U) :
    PairedPELQuotientIso (A.pullback (h ≫ f)).quotient ((A.pullback f).pullback h).quotient where
  source := PEL.Objects.PELIso.pullbackComp A.source f h
  target := PEL.Objects.PELIso.pullbackComp A.target f h
  forward_square := by
    change (Over.pullback (h.left ≫ f.left)).map A.quotient.forward.isogeny.hom ≫
        (A.target.polarized.abelian.pullbackCompIso f.left h.left).hom =
      (A.source.polarized.abelian.pullbackCompIso f.left h.left).hom ≫
        (Over.pullback h.left).map ((Over.pullback f.left).map A.quotient.forward.isogeny.hom)
    rw [HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom, HilbertConstruction.Abelian.Schemes.AbelianScheme.pullbackCompIso_hom]
    exact (Over.pullbackComp h.left f.left).hom.naturality A.quotient.forward.isogeny.hom

def pairedPELSetoid (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (N n : ℕ) (T : Over (Spec (.of K))) : Setoid (PairedPELObject P iota N n T) where
  r A B := Nonempty (PairedPELQuotientIso A.quotient B.quotient)
  iseqv := {
    refl A := ⟨PairedPELQuotientIso.refl A.quotient⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

def PairedPELClasses (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (N n : ℕ) (T : Over (Spec (.of K))) := Quotient (pairedPELSetoid P iota N n T)

def PairedPELObject.classOf (A : PairedPELObject P iota N n T) :
    PairedPELClasses P iota N n T := Quotient.mk _ A

namespace PairedPELClasses

def pullback (f : U ⟶ T) : PairedPELClasses P iota N n T → PairedPELClasses P iota N n U :=
  Quotient.map (fun A => A.pullback f) (fun _ _ ⟨e⟩ => ⟨e.pullback f⟩)

theorem pullback_id (q : PairedPELClasses P iota N n T) : PairedPELClasses.pullback (𝟙 T) q = q := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨A.pullbackIdIso⟩

theorem pullback_comp (f : U ⟶ T) (h : V ⟶ U) (q : PairedPELClasses P iota N n T) :
    PairedPELClasses.pullback (h ≫ f) q = PairedPELClasses.pullback h (PairedPELClasses.pullback f q) := by
  induction q using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨A.pullbackCompIso f h⟩

def swap : PairedPELClasses P iota N n T → PairedPELClasses P iota N n T :=
  Quotient.map PairedPELObject.swap (fun _ _ ⟨e⟩ => ⟨e.swap⟩)

theorem swap_swap (q : PairedPELClasses P iota N n T) : PairedPELClasses.swap (PairedPELClasses.swap q) = q := by
  induction q using Quotient.inductionOn with
  | h A => rfl

theorem pullback_swap (f : U ⟶ T) (q : PairedPELClasses P iota N n T) :
    PairedPELClasses.pullback f (PairedPELClasses.swap q) = PairedPELClasses.swap (PairedPELClasses.pullback f q) := by
  induction q using Quotient.inductionOn with
  | h A => rfl

def source : PairedPELClasses P iota N n T → PEL.Objects.PELClasses P iota N T :=
  Quotient.lift (fun A => A.source.classOf) (fun _ _ ⟨e⟩ => Quotient.sound ⟨e.source⟩)

def target : PairedPELClasses P iota N n T → PEL.Objects.PELClasses P iota N T :=
  Quotient.lift (fun A => A.target.classOf) (fun _ _ ⟨e⟩ => Quotient.sound ⟨e.target⟩)

theorem source_swap (q : PairedPELClasses P iota N n T) : PairedPELClasses.source (PairedPELClasses.swap q) = PairedPELClasses.target q := by
  induction q using Quotient.inductionOn with
  | h A => rfl

theorem target_swap (q : PairedPELClasses P iota N n T) : PairedPELClasses.target (PairedPELClasses.swap q) = PairedPELClasses.source q := by
  induction q using Quotient.inductionOn with
  | h A => rfl

theorem source_pullback (f : U ⟶ T) (q : PairedPELClasses P iota N n T) :
    PairedPELClasses.source (PairedPELClasses.pullback f q) = PEL.Objects.PELClasses.pullback f (PairedPELClasses.source q) := by
  induction q using Quotient.inductionOn with
  | h A => rfl

theorem target_pullback (f : U ⟶ T) (q : PairedPELClasses P iota N n T) :
    PairedPELClasses.target (PairedPELClasses.pullback f q) = PEL.Objects.PELClasses.pullback f (PairedPELClasses.target q) := by
  induction q using Quotient.inductionOn with
  | h A => rfl

end PairedPELClasses

def pairedPELModuliFunctor (P : Datum.RankThreePELDatum E s) (iota : E →+* K) (N n : ℕ) :
    (Over (Spec (.of K)))ᵒᵖ ⥤ Type 1 where
  obj T := PairedPELClasses P iota N n T.unop
  map f := TypeCat.ofHom (PairedPELClasses.pullback f.unop)
  map_id _ := by
    ext q
    exact PairedPELClasses.pullback_id q
  map_comp f h := by
    ext q
    exact PairedPELClasses.pullback_comp f.unop h.unop q

def pairedPELSource : pairedPELModuliFunctor P iota N n ⟶ PEL.Classifying.pelModuliFunctor P iota N where
  app _ := TypeCat.ofHom PairedPELClasses.source
  naturality _ _ f := by
    ext q
    exact PairedPELClasses.source_pullback f.unop q

def pairedPELTarget : pairedPELModuliFunctor P iota N n ⟶ PEL.Classifying.pelModuliFunctor P iota N where
  app _ := TypeCat.ofHom PairedPELClasses.target
  naturality _ _ f := by
    ext q
    exact PairedPELClasses.target_pullback f.unop q

def pairedPELSwap : pairedPELModuliFunctor P iota N n ⟶ pairedPELModuliFunctor P iota N n where
  app _ := TypeCat.ofHom PairedPELClasses.swap
  naturality _ _ f := by
    ext q
    exact (PairedPELClasses.pullback_swap f.unop q).symm

theorem pairedPELSwap_involutive :
    pairedPELSwap (P := P) (iota := iota) (N := N) (n := n) ≫ pairedPELSwap = 𝟙 _ := by
  ext T q
  exact PairedPELClasses.swap_swap q

theorem pairedPELSwap_source :
    pairedPELSwap (P := P) (iota := iota) (N := N) (n := n) ≫ pairedPELSource = pairedPELTarget := by
  ext T q
  exact PairedPELClasses.source_swap q

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Paired.PELFunctor
