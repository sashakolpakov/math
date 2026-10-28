import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckePairClassSurjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckeFixedSourceClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FinePELPointClassification

/-! # Hecke Etale -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily
open _root_.CategoryTheory
open _root_.AlgebraicGeometry
section

/-! The actual finite etale kernel parameter represents typed paired
PEL quotients on all test schemes. Fineness fixes the source map and
full-level rigidity fixes the original kernel inside that source. -/

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (Z : Models.FinePELModel P iota N) (hZ : Z.IsFine)
    [IsLocallyNoetherian Z.space.left] [LocallyOfFiniteType Z.space.hom]
    (hN : 3 ≤ N) {hn : 0 < n}
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (R : NoetherianPairedHeckeSource.PairedHeckeSource Z.universal n hn M)

include hZ hN hdegree

theorem NoetherianPairedHeckeSource.PairedHeckeSource.classifying_injective (X : Over (Spec (.of K))) :
    Function.Injective (fun f : X ⟶ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter =>
      TypedPairedPEL.TypedPairedPELClasses.pullback M f R.classOf) := by
  intro c d h
  obtain ⟨e⟩ : Nonempty (Paired.PELFunctor.PairedPELQuotientIso (R.quotient.pullback c) (R.quotient.pullback d)) :=
    Quotient.exact (congrArg Subtype.val h)
  let p := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space R.parameter
  have hs : d ≫ p = c ≫ p := by
    apply (Z.familyClassifying_bijective hZ X).injective
    apply (PEL.Objects.PELObject.classOf_eq_iff _ _).mpr
    exact ⟨((PEL.Objects.PELIso.pullbackComp Z.universal p d).trans e.source.symm).trans
      (PEL.Objects.PELIso.pullbackComp Z.universal p c).symm⟩
  let Q : Over Z.space.left := Over.mk (c ≫ p).left
  let k : Q ⟶ R.parameter := Over.homMk c.left rfl
  let l : Q ⟶ R.parameter := Over.homMk d.left (congrArg Over.Hom.left hs)
  let e' : Paired.PELFunctor.PairedPELQuotientIso (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k))
      (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap l)) := {
    source := { polarized := e.source.polarized, action := e.source.action }
    target := { polarized := e.target.polarized, action := e.target.action }
    forward_square := e.forward_square }
  let a := (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap k)).precomposeIso
    (PEL.ParameterPullbackComparison.pelParameterPullbackIso Z.universal k).symm
  let b := (R.quotient.pullback (PEL.ParameterPullbackComparison.parameterTotalMap l)).precomposeIso
    (PEL.ParameterPullbackComparison.pelParameterPullbackIso Z.universal l).symm
  have hkl : R.classAtParameter k = R.classAtParameter l :=
    Subtype.ext (Quotient.sound ⟨(a.trans e').trans b.symm⟩)
  have heq := R.classAtParameter_injective hN hdegree hkl
  have hh : c.left = d.left := congrArg (fun u : Q ⟶ R.parameter => u.left) heq
  exact Over.OverMorphism.ext hh

theorem NoetherianPairedHeckeSource.PairedHeckeSource.classifying_bijective (X : Over (Spec (.of K))) :
    Function.Bijective (fun f : X ⟶ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter =>
      TypedPairedPEL.TypedPairedPELClasses.pullback M f R.classOf) :=
  ⟨R.classifying_injective Z hZ hN hdegree M X,
    R.classifying_surjective Z hZ hdegree M X⟩

theorem NoetherianPairedHeckeSource.PairedHeckeSource.classifying_isIso : IsIso (R.classifying Z M) := by
  apply (NatTrans.isIso_iff_isIso_app (R.classifying Z M)).mpr
  intro X
  apply (ConcreteCategory.isIso_iff_bijective ((R.classifying Z M).app X)).mpr
  have h := R.classifying_bijective Z hZ hN hdegree M X.unop
  constructor
  · intro a b hab
    apply ULift.ext
    exact h.injective hab
  · intro q
    obtain ⟨f, hf⟩ := h.surjective q
    exact ⟨ULift.up f, hf⟩

def NoetherianPairedHeckeSource.PairedHeckeSource.moduliIso :
    uliftYoneda.{1}.obj (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter) ≅
      TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M := by
  let : IsIso (R.classifying Z M) := R.classifying_isIso Z hZ hN hdegree M
  exact asIso (R.classifying Z M)

theorem NoetherianPairedHeckeSource.PairedHeckeSource.moduliIso_hom :
    (R.moduliIso Z hZ hN hdegree M).hom = R.classifying Z M := rfl

end

section

/-! The proved representation of typed paired PEL quotients turns
their literal swap into an actual involution of the finite etale
parameter scheme. No involution or target-map comparison is assumed. -/

open scoped BigOperators

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Type) [AddCommGroup M]

def HeckeEtale.typedPairedPELSwapIso (hn : 0 < n)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2)) :
    TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M ≅ TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M where
  hom := TypedPairedPEL.typedPairedPELSwap M hn hdegree
  inv := TypedPairedPEL.typedPairedPELSwap M hn hdegree
  hom_inv_id := TypedPairedPEL.typedPairedPELSwap_involutive M hn hdegree
  inv_hom_id := TypedPairedPEL.typedPairedPELSwap_involutive M hn hdegree

variable (Z : Models.FinePELModel P iota N) (hZ : Z.IsFine)
    [IsLocallyNoetherian Z.space.left] [LocallyOfFiniteType Z.space.hom]
    (hN : 3 ≤ N) {hn : 0 < n}
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    [Module (ZMod n) M] [Finite M]
    (R : NoetherianPairedHeckeSource.PairedHeckeSource Z.universal n hn M)

def NoetherianPairedHeckeSource.PairedHeckeSource.swapIso :
    AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter ≅ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter :=
  (uliftYoneda.{1}).preimageIso
    (R.moduliIso Z hZ hN hdegree M ≪≫ HeckeEtale.typedPairedPELSwapIso M hn hdegree ≪≫
      (R.moduliIso Z hZ hN hdegree M).symm)

theorem NoetherianPairedHeckeSource.PairedHeckeSource.swapIso_map_hom :
    uliftYoneda.{1}.map (R.swapIso M Z hZ hN hdegree).hom =
      (R.moduliIso Z hZ hN hdegree M).hom ≫ TypedPairedPEL.typedPairedPELSwap M hn hdegree ≫
        (R.moduliIso Z hZ hN hdegree M).inv := by
  change uliftYoneda.{1}.map (uliftYoneda.{1}.preimage _) = _
  simp only [Functor.map_preimage, Iso.trans_hom, Iso.symm_hom,
    HeckeEtale.typedPairedPELSwapIso]

theorem NoetherianPairedHeckeSource.PairedHeckeSource.swapIso_inv_eq_hom :
    (R.swapIso M Z hZ hN hdegree).inv = (R.swapIso M Z hZ hN hdegree).hom := by
  apply uliftYoneda.{1}.map_injective
  change uliftYoneda.{1}.map (uliftYoneda.{1}.preimage _) =
    uliftYoneda.{1}.map (uliftYoneda.{1}.preimage _)
  simp only [Functor.map_preimage, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, HeckeEtale.typedPairedPELSwapIso, Category.assoc]

theorem NoetherianPairedHeckeSource.PairedHeckeSource.swapIso_involutive :
    (R.swapIso M Z hZ hN hdegree).hom ≫ (R.swapIso M Z hZ hN hdegree).hom = 𝟙 _ := by
  simpa only [R.swapIso_inv_eq_hom M Z hZ hN hdegree] using
    (R.swapIso M Z hZ hN hdegree).hom_inv_id

theorem NoetherianPairedHeckeSource.PairedHeckeSource.swapIso_classifying :
    uliftYoneda.{1}.map (R.swapIso M Z hZ hN hdegree).hom ≫ R.classifying Z M =
      R.classifying Z M ≫ TypedPairedPEL.typedPairedPELSwap M hn hdegree := by
  let j := R.moduliIso Z hZ hN hdegree M
  change uliftYoneda.{1}.map (R.swapIso M Z hZ hN hdegree).hom ≫ j.hom =
    j.hom ≫ TypedPairedPEL.typedPairedPELSwap M hn hdegree
  rw [R.swapIso_map_hom M Z hZ hN hdegree]
  dsimp only [j]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem NoetherianPairedHeckeSource.PairedHeckeSource.swapIso_pairClass :
    TypedPairedPEL.TypedPairedPELClasses.pullback M (R.swapIso M Z hZ hN hdegree).hom R.classOf =
      TypedPairedPEL.TypedPairedPELClasses.swap M hn hdegree R.classOf := by
  let Q := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter
  have h := congrArg (fun a => a.app (.op Q) (ULift.up (𝟙 Q)))
    (R.swapIso_classifying M Z hZ hN hdegree)
  change TypedPairedPEL.TypedPairedPELClasses.pullback M (𝟙 Q ≫ (R.swapIso M Z hZ hN hdegree).hom) R.classOf =
    TypedPairedPEL.TypedPairedPELClasses.swap M hn hdegree (TypedPairedPEL.TypedPairedPELClasses.pullback M (𝟙 Q) R.classOf) at h
  rw [Category.id_comp, TypedPairedPEL.TypedPairedPELClasses.pullback_id] at h
  exact h

end

/-! The actual target moduli morphism is the source projection
composed with the constructed paired-quotient involution. Hence both
projections of the original correspondence are finite etale. -/

open scoped BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N n : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (Z : Models.FinePELModel P iota N) (hZ : Z.IsFine)
    [IsLocallyNoetherian Z.space.left] [LocallyOfFiniteType Z.space.hom]
    (hN : 3 ≤ N) {hn : 0 < n}
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    (R : NoetherianPairedHeckeSource.PairedHeckeSource Z.universal n hn M)

def NoetherianPairedHeckeSource.PairedHeckeSource.targetProjection : AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter ⟶ Z.space :=
  AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingMap Z hZ R.target

theorem NoetherianPairedHeckeSource.PairedHeckeSource.swapIso_source :
    (R.swapIso M Z hZ hN hdegree).hom ≫ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space R.parameter =
      R.targetProjection Z hZ := by
  let Q := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter
  let p := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space R.parameter
  let σ := (R.swapIso M Z hZ hN hdegree).hom
  have h := congrArg (fun q => Paired.PELFunctor.PairedPELClasses.source q.val)
    (R.swapIso_pairClass M Z hZ hN hdegree)
  change ((Z.universal.pullback p).pullback σ).classOf = R.target.classOf at h
  apply (Z.familyClassifying_bijective hZ Q).injective
  calc
    (Z.universal.pullback (σ ≫ p)).classOf = ((Z.universal.pullback p).pullback σ).classOf :=
      (PEL.Objects.PELObject.classOf_eq_iff _ _).mpr ⟨PEL.Objects.PELIso.pullbackComp Z.universal p σ⟩
    _ = R.target.classOf := h
    _ = (Z.universal.pullback (R.targetProjection Z hZ)).classOf :=
      (PEL.Objects.PELObject.classOf_eq_iff _ _).mpr ⟨(AbelianScheme.IsogenyQuotient.FinePELTarget.Construction.finePELClassifyingIso Z hZ R.target).toPELIso⟩

include hN hdegree in
theorem NoetherianPairedHeckeSource.PairedHeckeSource.targetProjection_finite_etale :
    IsFinite (R.targetProjection Z hZ).left ∧ Etale (R.targetProjection Z hZ).left := by
  let : IsFinite R.parameter.hom := R.finite
  let : Etale R.parameter.hom := R.etale
  let : IsIso (R.swapIso M Z hZ hN hdegree).hom.left :=
    (Over.forget (Spec (.of K))).map_isIso (R.swapIso M Z hZ hN hdegree).hom
  rw [← R.swapIso_source Z hZ hN hdegree M]
  change IsFinite ((R.swapIso M Z hZ hN hdegree).hom.left ≫ R.parameter.hom) ∧
    Etale ((R.swapIso M Z hZ hN hdegree).hom.left ≫ R.parameter.hom)
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily

namespace AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckeEtale

/-! Construct the actual paired Hecke correspondence from the given
fine PEL model. Both projections are finite etale, the fixed kernel
type is retained, and the source-target involution is proved from the
all-test moduli representation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

theorem exists_finite_etale_paired_hecke_correspondence
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] [Field K] [NumberField K] [CharZero K]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (Z : Models.FinePELModel P iota N) (hZ : Z.IsFine)
    [IsLocallyNoetherian Z.space.left] [LocallyOfFiniteType Z.space.hom]
    (hN : 3 ≤ N) (n : ℕ) (hn : 0 < n) (hcop : Nat.Coprime n N)
    (hmod : Nat.ModEq N n 1)
    (hdegree : Nat.Coprime n ((∏ i, P.polarizationType i) ^ 2))
    (M : Type) [AddCommGroup M] [Module (ZMod n) M] [Finite M] :
    ∃ R : NoetherianPairedHeckeSource.PairedHeckeSource Z.universal n hn M,
      IsFinite (R.targetProjection Z hZ).left ∧ Etale (R.targetProjection Z hZ).left ∧
      Nonempty (uliftYoneda.{1}.obj (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter) ≅
        TypedPairedPEL.typedPairedPELModuliFunctor P iota N n M) ∧
      ∃ σ : AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter ≅ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameter Z.space R.parameter,
        σ.hom ≫ σ.hom = 𝟙 _ ∧
          σ.hom ≫ AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource Z.space R.parameter = R.targetProjection Z hZ := by
  obtain ⟨R⟩ := NoetherianPairedHeckeSource.exists_noetherian_paired_hecke_source Z.universal n hn hcop hmod hdegree M
  have ht := R.targetProjection_finite_etale Z hZ hN hdegree M
  exact ⟨R, ht.1, ht.2, ⟨R.moduliIso Z hZ hN hdegree M⟩,
    R.swapIso M Z hZ hN hdegree, R.swapIso_involutive M Z hZ hN hdegree,
    R.swapIso_source Z hZ hN hdegree M⟩

end AlgebraicGeometry.AbelianModuli.ReferenceFamily.HeckeEtale

end

end OAI
