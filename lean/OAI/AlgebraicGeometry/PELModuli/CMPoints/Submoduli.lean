import OAI.AlgebraicGeometry.PELModuli.CMPoints.Fine

/-! # Submoduli -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Submoduli

noncomputable section

/-! A monomorphic subspace of the fine PEL model represents its actual
enhanced moduli image. This applies to the reduced generic model in IntegralModel,
whose finiteness properties come from the integral model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v w

def representableRangeOfInjective
    {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type (max v w)} {X : C}
    (α : uliftYoneda.{w}.obj X ⟶ F) (hα : ∀ T, Function.Injective (α.app T)) :
    (Subfunctor.range α).toFunctor.RepresentableBy X := by
  let β := Subfunctor.toRange α
  let hβ : IsIso β := (NatTrans.isIso_iff_isIso_app β).mpr (fun T =>
    (CategoryTheory.isIso_iff_bijective (β.app T)).mpr (by
      constructor
      · intro x y h
        exact hα T (congrArg Subtype.val h)
      · rintro ⟨y, x, hx⟩
        exact ⟨x, Subtype.ext hx⟩))
  exact (Functor.representableByUliftFunctorEquiv.symm
    (Functor.RepresentableBy.yoneda X)).ofIso (@asIso _ _ _ _ β hβ)

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K]
  {s N r : ℕ} {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (b : Module.Basis (Fin r) ℤ (NumberField.RingOfIntegers E))
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (hM : M.IsFine)
  {X : Over (Spec (.of K))} (f : X ⟶ M.space)

def pelSubspaceClassifier :
    uliftYoneda.{1}.obj X ⟶ ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.enhancedAbelianModuliOver (3 * s) P.polarizationType N r (Spec (.of K)) :=
  uliftYoneda.map f ≫
    ((Functor.RepresentableBy.equivUliftYonedaIso (AbelianModuli.ReferenceFamily.PEL.Classifying.pelModuliFunctor P iota N) M.space)
      (Enhancement.pelRepresentable M hM)).hom ≫ Enhancement.pelEnhancementTransformation b

theorem pelSubspaceClassifier_injective [Mono f] (T : (Over (Spec (.of K)))ᵒᵖ) :
    Function.Injective ((pelSubspaceClassifier b M hM f).app T) := by
  intro x y h
  apply ULift.ext
  change Enhancement.pelEnhancementClasses b ((M.universal.pullback (x.down ≫ f)).classOf) =
    Enhancement.pelEnhancementClasses b ((M.universal.pullback (y.down ≫ f)).classOf) at h
  exact (cancel_mono f).mp ((Enhancement.pelClassifying_bijective M hM T.unop).1
    (Enhancement.pelEnhancementClasses_injective b h))

def pelSubspaceLocus :
    Subfunctor (ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.enhancedAbelianModuliOver (3 * s) P.polarizationType N r (Spec (.of K))) :=
  Subfunctor.range (pelSubspaceClassifier b M hM f)

def pelSubspaceRepresentable [Mono f] :
    (pelSubspaceLocus b M hM f).toFunctor.RepresentableBy X :=
  representableRangeOfInjective _ (pelSubspaceClassifier_injective b M hM f)

def pelArithmeticSubmoduli
    (K0 : Subfield ℂ) [NumberField K0] {iota0 : E →+* K0}
    (M0 : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota0 N) (hP : P.IsAdmissible) (hN : 3 ≤ N)
    (hM0 : M0.IsFine) {X0 : Over (Spec (.of K0))} (f0 : X0 ⟶ M0.space) [Mono f0]
    (hfinite : LocallyOfFiniteType X0.hom) : ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli where
  dimension := 3 * s
  polarizationType := P.polarizationType
  polarizationType_pos := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩ := hP
    exact hpos
  polarizationType_chain := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hchain, _⟩ := hP
    exact hchain
  level := N
  deepLevel := hN
  endomorphismCount := r
  baseField := K0
  numberField := inferInstance
  parameter := X0
  locallyFiniteType := hfinite
  locus := pelSubspaceLocus b M0 hM0 f0
  represents := pelSubspaceRepresentable b M0 hM0 f0

theorem pelArithmeticSubmoduli_universalClass
    (K0 : Subfield ℂ) [NumberField K0] {iota0 : E →+* K0}
    (M0 : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota0 N) (hP : P.IsAdmissible) (hN : 3 ≤ N)
    (hM0 : M0.IsFine) {X0 : Over (Spec (.of K0))} (f0 : X0 ⟶ M0.space) [Mono f0]
    (hfinite : LocallyOfFiniteType X0.hom) :
    (pelArithmeticSubmoduli b K0 M0 hP hN hM0 f0 hfinite).universalClass =
      (Enhancement.pelEnhancement b (M0.universal.pullback f0)).classOf := by
  change Enhancement.pelEnhancementClasses b ((M0.universal.pullback ((𝟙 X0) ≫ f0)).classOf) = _
  rw [Category.id_comp]
  rfl

theorem pelArithmeticSubmoduli_universalIso
    (K0 : Subfield ℂ) [NumberField K0] {iota0 : E →+* K0}
    (M0 : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota0 N) (hP : P.IsAdmissible) (hN : 3 ≤ N)
    (hM0 : M0.IsFine) {X0 : Over (Spec (.of K0))} (f0 : X0 ⟶ M0.space) [Mono f0]
    (hfinite : LocallyOfFiniteType X0.hom) :
    Nonempty (ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianIso
      (pelArithmeticSubmoduli b K0 M0 hP hN hM0 f0 hfinite).universal
      (Enhancement.pelEnhancement b (M0.universal.pullback f0))) := by
  apply (ArithmeticGeometry.Descent.CMVariety.ModuliObjects.Abelian.EnhancedAbelianData.classOf_eq_iff _ _).mp
  exact (ArithmeticGeometry.Descent.CMVariety.StandardModuli.Abelian.ArithmeticAbelianModuli.universal_classOf _).trans
    (pelArithmeticSubmoduli_universalClass b K0 M0 hP hN hM0 f0 hfinite)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Submoduli
