import OAI.ArithmeticGeometry.Descent.CMVariety.AffineSmoothSpread
import OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport

/-! # Smooth Arithmetic -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothArithmetic.Abelian

noncomputable section

section

/-!
Every complex point of a locally finite-type rational scheme factors
through a smooth integral rational scheme that maps monomorphically into
the original scheme. The construction handles singular and nonreduced
parameter schemes by taking the kernel of the actual affine evaluation.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport

theorem complex_point_has_smooth_arithmetic_factor
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType f]
    (p : Spec (CommRingCat.of ℂ) ⟶ X) :
    ∃ (Y : Scheme) (g : Y ⟶ Spec (CommRingCat.of ℚ))
      (i : Y ⟶ X) (q : Spec (CommRingCat.of ℂ) ⟶ Y),
      IsIntegral Y ∧ Smooth g ∧ Mono i ∧ i ≫ f = g ∧ q ≫ i = p := by
  obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p (IsLocalRing.closedPoint ℂ) ∈ (⊤ : X.Opens) from trivial)
  let A := Γ(X, U)
  let : Algebra ℚ A := AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let j := hU.fromSpec
  have hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) :=
    (AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU).symm
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) := by
    rw [← hj]
    infer_instance
  let : Algebra.FiniteType ℚ A := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft)
  have hrange : Set.range p ⊆ Set.range j := by
    rintro z ⟨w, rfl⟩
    have hw : w = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    rw [hw]
    change p (IsLocalRing.closedPoint ℂ) ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hpU
  let pA := IsOpenImmersion.lift j p hrange
  have hpA : pA ≫ j = p := IsOpenImmersion.lift_fac _ _ _
  let xRing := (Spec.preimage pA).hom
  let x : A →ₐ[ℚ] ℂ :=
    { xRing with commutes' := fun c =>
      DFunLike.congr_fun (show xRing.comp (algebraMap ℚ A) = algebraMap ℚ ℂ from Subsingleton.elim _ _) c }
  obtain ⟨Y, g, i, q, hY, hg, hi, hif, hqi⟩ := AffineSmoothSpread.Abelian.affine_complex_point_has_smooth_arithmetic_factor x
  let : Mono i := hi
  refine ⟨Y, g, i ≫ j, q, hY, hg, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hj, hif]
  · rw [← Category.assoc, hqi]
    have hx : Spec.map (CommRingCat.ofHom x.toRingHom) = pA := Spec.map_preimage pA
    rw [hx, hpA]

end

section

/-! Retain arithmetic genericity in the constructed smooth integral factor
of a complex point. This supplies injective coefficient evaluation later. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport

theorem generic_complex_point_of_open_factor
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (i : Y ⟶ X) [IsOpenImmersion i]
    (p : Spec (CommRingCat.of ℂ) ⟶ X) (q : Spec (CommRingCat.of ℂ) ⟶ Y)
    (hq : q ≫ i = p) (hp : p (IsLocalRing.closedPoint ℂ) = genericPoint X) :
    q (IsLocalRing.closedPoint ℂ) = genericPoint Y := by
  apply i.isOpenEmbedding.injective
  calc
    i (q (IsLocalRing.closedPoint ℂ)) = (q ≫ i) (IsLocalRing.closedPoint ℂ) := rfl
    _ = p (IsLocalRing.closedPoint ℂ) := congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) hq
    _ = genericPoint X := hp
    _ = i (genericPoint Y) := (genericPoint_eq_of_isOpenImmersion i).symm

theorem affine_complex_point_has_generic_smooth_arithmetic_factor
    {A : Type} [CommRing A] [Algebra ℚ A] [Algebra.FiniteType ℚ A] (x : A →ₐ[ℚ] ℂ) :
    ∃ (Y : Scheme) (f : Y ⟶ Spec (CommRingCat.of ℚ))
      (i : Y ⟶ Spec (CommRingCat.of A)) (q : Spec (CommRingCat.of ℂ) ⟶ Y),
      IsIntegral Y ∧ Smooth f ∧ Mono i ∧
      i ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) = f ∧
      q ≫ i = Spec.map (CommRingCat.ofHom x.toRingHom) ∧
      IsGenericPoint (q (IsLocalRing.closedPoint ℂ)) Set.univ := by
  let I := RingHom.ker x
  let B := A ⧸ I
  let : I.IsPrime := RingHom.ker_isPrime x
  let φ : B →ₐ[ℚ] ℂ := Ideal.kerLiftAlg x
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective x
  let fB := Spec.map (CommRingCat.ofHom (algebraMap ℚ B))
  let p := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let j := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let : Algebra.FinitePresentation ℚ B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : LocallyOfFinitePresentation fB :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hp : p (IsLocalRing.closedPoint ℂ) = genericPoint (Spec (CommRingCat.of B)) := by
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change Ideal.comap φ.toRingHom (IsLocalRing.maximalIdeal ℂ) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ.toRingHom).mp hφ
  obtain ⟨U, hU, hSmooth, q, hq⟩ := GenericSmoothNeighborhood.Abelian.generic_complex_point_factors_through_smooth_open fB p hp
  let : IsIntegral U := hU
  let : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective
  have hj : j ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) = fB := by
    rw [← Spec.map_comp]
    rfl
  have hx : p ≫ j = Spec.map (CommRingCat.ofHom x.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  have hgen := generic_complex_point_of_open_factor U.ι p q hq hp
  refine ⟨U, U.ι ≫ fB, U.ι ≫ j, q, hU, hSmooth, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, hj]
  · rw [← Category.assoc, hq, hx]
  · rw [hgen]
    exact genericPoint_spec U

theorem complex_point_has_generic_smooth_arithmetic_factor
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType f]
    (p : Spec (CommRingCat.of ℂ) ⟶ X) :
    ∃ (Y : Scheme) (g : Y ⟶ Spec (CommRingCat.of ℚ))
      (i : Y ⟶ X) (q : Spec (CommRingCat.of ℂ) ⟶ Y),
      IsIntegral Y ∧ Smooth g ∧ Mono i ∧ i ≫ f = g ∧ q ≫ i = p ∧
      IsGenericPoint (q (IsLocalRing.closedPoint ℂ)) Set.univ := by
  obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p (IsLocalRing.closedPoint ℂ) ∈ (⊤ : X.Opens) from trivial)
  let A := Γ(X, U)
  let : Algebra ℚ A := AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let j := hU.fromSpec
  have hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) :=
    (AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU).symm
  have hft : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℚ A))) := by
    rw [← hj]
    infer_instance
  let : Algebra.FiniteType ℚ A := RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hft)
  have hrange : Set.range p ⊆ Set.range j := by
    rintro z ⟨w, rfl⟩
    have hw : w = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    rw [hw]
    change p (IsLocalRing.closedPoint ℂ) ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hpU
  let pA := IsOpenImmersion.lift j p hrange
  have hpA : pA ≫ j = p := IsOpenImmersion.lift_fac _ _ _
  let xRing := (Spec.preimage pA).hom
  let x : A →ₐ[ℚ] ℂ :=
    { xRing with commutes' := fun c =>
      DFunLike.congr_fun (show xRing.comp (algebraMap ℚ A) = algebraMap ℚ ℂ from Subsingleton.elim _ _) c }
  obtain ⟨Y, g, i, q, hY, hg, hi, hif, hqi, hgen⟩ :=
    affine_complex_point_has_generic_smooth_arithmetic_factor x
  let : Mono i := hi
  refine ⟨Y, g, i ≫ j, q, hY, hg, inferInstance, ?_, ?_, hgen⟩
  · rw [Category.assoc, hj, hif]
  · rw [← Category.assoc, hqi]
    have hx : Spec.map (CommRingCat.ofHom x.toRingHom) = pA := Spec.map_preimage pA
    rw [hx, hpA]

end

/-!
Construct an actual smooth finite-type rational coefficient ring for an
arbitrary arithmetic complex point, with injective evaluation into the
complex numbers and a monomorphism to the original parameter scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport

structure SmoothArithmeticChart {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) (p : Spec (CommRingCat.of ℂ) ⟶ X) where
  ring : Type
  [commRing : CommRing ring]
  [algebra : Algebra ℚ ring]
  [domain : IsDomain ring]
  smooth : Algebra.Smooth ℚ ring
  point : ring →ₐ[ℚ] ℂ
  injective : Function.Injective point
  map : Spec (CommRingCat.of ring) ⟶ X
  mono : Mono map
  structure_eq : map ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ ring))
  recovers : Spec.map (CommRingCat.ofHom point.toRingHom) ≫ map = p

attribute [instance] SmoothArithmeticChart.commRing SmoothArithmeticChart.algebra
  SmoothArithmeticChart.domain SmoothArithmeticChart.smooth SmoothArithmeticChart.mono

theorem smooth_generic_point_has_arithmetic_chart
    {X : Scheme} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [Smooth f]
    (p : Spec (CommRingCat.of ℂ) ⟶ X)
    (hgeneric : IsGenericPoint (p (IsLocalRing.closedPoint ℂ)) Set.univ) :
    Nonempty (SmoothArithmeticChart f p) := by
  have hpg : p (IsLocalRing.closedPoint ℂ) = genericPoint X := hgeneric.eq (genericPoint_spec X)
  obtain ⟨U, hU, hpU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p (IsLocalRing.closedPoint ℂ) ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨p (IsLocalRing.closedPoint ℂ), hpU⟩⟩
  let R := Γ(X, U)
  let : Algebra ℚ R := AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarAlgebra f U
  let j := hU.fromSpec
  have hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℚ R)) :=
    (AlgebraicGeometry.Foundations.Scheme.SpecScalarTransport.specSectionScalarMap_fromSpec f U hU).symm
  have hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℚ R))) := by
    rw [← hj]
    infer_instance
  let : Algebra.Smooth ℚ R := RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
  have hrange : Set.range p ⊆ Set.range j := by
    rintro z ⟨w, rfl⟩
    have hw : w = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    rw [hw]
    change p (IsLocalRing.closedPoint ℂ) ∈ Set.range hU.fromSpec
    rw [hU.range_fromSpec]
    exact hpU
  let pR := IsOpenImmersion.lift j p hrange
  have hpR : pR ≫ j = p := IsOpenImmersion.lift_fac _ _ _
  let xRing := (Spec.preimage pR).hom
  let x : R →ₐ[ℚ] ℂ :=
    { xRing with commutes' := fun c =>
      DFunLike.congr_fun (show xRing.comp (algebraMap ℚ R) = algebraMap ℚ ℂ from Subsingleton.elim _ _) c }
  have hx : Spec.map (CommRingCat.ofHom x.toRingHom) = pR := Spec.map_preimage pR
  have hxgeneric : (Spec.map (CommRingCat.ofHom x.toRingHom)) (IsLocalRing.closedPoint ℂ) =
      genericPoint (Spec (CommRingCat.of R)) := by
    rw [hx]
    exact generic_complex_point_of_open_factor j p pR hpR hpg
  have hxin : Function.Injective x := by
    rw [genericPoint_eq_bot_of_affine] at hxgeneric
    have h := congrArg PrimeSpectrum.asIdeal hxgeneric
    change Ideal.comap x.toRingHom (IsLocalRing.maximalIdeal ℂ) = ⊥ at h
    rw [IsLocalRing.maximalIdeal_eq_bot] at h
    exact (RingHom.injective_iff_ker_eq_bot x.toRingHom).mpr h
  refine ⟨{
    ring := R
    smooth := inferInstance
    point := x
    injective := hxin
    map := j
    mono := inferInstance
    structure_eq := hj
    recovers := ?_ }⟩
  rw [hx]
  exact hpR

theorem complex_point_has_smooth_arithmetic_chart
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [LocallyOfFiniteType f]
    (p : Spec (CommRingCat.of ℂ) ⟶ X) : Nonempty (SmoothArithmeticChart f p) := by
  obtain ⟨Y, g, i, q, hY, hg, hi, hif, hqi, hgeneric⟩ :=
    complex_point_has_generic_smooth_arithmetic_factor f p
  let : IsIntegral Y := hY
  let : Smooth g := hg
  let : Mono i := hi
  obtain ⟨C⟩ := smooth_generic_point_has_arithmetic_chart g q hgeneric
  refine ⟨{
    ring := C.ring
    smooth := C.smooth
    point := C.point
    injective := C.injective
    map := C.map ≫ i
    mono := inferInstance
    structure_eq := ?_
    recovers := ?_ }⟩
  · rw [Category.assoc, hif, C.structure_eq]
  · rw [← Category.assoc, C.recovers, hqi]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothArithmetic.Abelian
