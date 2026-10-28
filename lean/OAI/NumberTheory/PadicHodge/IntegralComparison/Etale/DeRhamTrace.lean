import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FreeTraceDerivation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateComplexIso
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryFormScalars
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryDeRhamFunctor

/-! # De Rham Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTrace

noncomputable section

/-! Ring trace gives a chain transfer on the actual de Rham complexes
of finite free maps between étale polynomial charts. -/

open _root_.CategoryTheory
open scoped TensorProduct

universe u v

variable (R A B σ : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Algebra (MvPolynomial σ R) A] [Algebra (MvPolynomial σ R) B]
  [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
  [IsScalarTower (MvPolynomial σ R) A B]
  [Algebra.FormallyEtale (MvPolynomial σ R) A]
  [Algebra.FormallyEtale (MvPolynomial σ R) B]
  [Fintype σ] [LinearOrder σ]

omit [Algebra R A] [Algebra R B] [IsScalarTower R A B]
    [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B]
    [Algebra.FormallyEtale (MvPolynomial σ R) A]
    [Algebra.FormallyEtale (MvPolynomial σ R) B] [Fintype σ] [LinearOrder σ] in
theorem coordinate_map (i : σ) :
    algebraMap A B (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ i) =
      AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R B σ i :=
  (IsScalarTower.algebraMap_apply (MvPolynomial σ R) A B (MvPolynomial.X i)).symm

omit [Fintype σ] in
theorem derivation_map (i : σ) (x : A) :
    AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R B σ i (algebraMap A B x) =
      algebraMap A B (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A σ i x) := by
  let D := AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A σ i
  let E := AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R B σ i
  have he : E.compAlgebraMapL R A B B = (Algebra.ofId A B).toLinearMap.compDer D := by
    apply AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.ext R A σ
    intro j
    change E (algebraMap A B (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ j)) =
      algebraMap A B (D (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ j))
    rw [coordinate_map]
    dsimp only [D, E]
    rw [AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation_coordinate,
      AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation_coordinate]
    split_ifs <;> simp only [map_one, map_zero]
  exact congrArg (fun F : Derivation R A B => F x) he

variable {ι : Type v} [Fintype ι] (b : Module.Basis ι A B)

include b in
omit [Fintype σ] in
theorem trace_derivation (i : σ) (x : B) :
    Algebra.trace A B (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R B σ i x) =
      AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A σ i (Algebra.trace A B x) :=
  Finite.FreeTraceDerivation.trace_derivation b
    (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A σ i)
    (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R B σ i) (derivation_map R A B σ i) x

def coordinateTrace : OrdinaryCoordinates.Ordinary.complex R B σ ⟶
    OrdinaryCoordinates.Ordinary.complex R A σ :=
  AlgebraicGeometry.Crystalline.Cohomology.Koszul.TensorMap.KoszulTensorMap.map R σ B A
    (fun i => (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R B σ i).toLinearMap)
    (fun i => (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.derivation R A σ i).toLinearMap)
    ((Algebra.trace A B).restrictScalars R) (trace_derivation R A B σ b)
    (CoordinateDerivations.commute R B σ)
    (CoordinateDerivations.commute R A σ)

def trace : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B ⟶ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A :=
  (CoordinateComplexIso.iso R B σ).inv ≫ coordinateTrace R A B σ b ≫
    (CoordinateComplexIso.iso R A σ).hom

theorem trace_coordinates (n : ℕ) (z : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ B n) :
    (DeRhamTrace.trace R A B σ b).f n ((CoordinateComplexIso.iso R B σ).hom.f n z) =
      (CoordinateComplexIso.iso R A σ).hom.f n
        (TensorProduct.map ((Algebra.trace A B).restrictScalars R) LinearMap.id z) := by
  have he := Iso.hom_inv_id_apply
    ((HomologicalComplex.eval (ModuleCat R) (.up ℕ) n).mapIso
      (CoordinateComplexIso.iso R B σ)) z
  change (CoordinateComplexIso.iso R B σ).inv.f n
    ((CoordinateComplexIso.iso R B σ).hom.f n z) = z at he
  change (CoordinateComplexIso.iso R A σ).hom.f n
    ((coordinateTrace R A B σ b).f n
      ((CoordinateComplexIso.iso R B σ).inv.f n
        ((CoordinateComplexIso.iso R B σ).hom.f n z))) = _
  rw [he]
  rfl

theorem trace_coordinate_symbol (n : ℕ) (x : B) (v : Fin n → σ) :
    (DeRhamTrace.trace R A B σ b).f n
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B x (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R B σ ∘ v)) =
    AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A (Algebra.trace A B x)
      (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v) := by
  rw [← CoordinateComplexIso.word R B σ n x v]
  rw [trace_coordinates]
  change (CoordinateComplexIso.iso R A σ).hom.f n
    (Algebra.trace A B x ⊗ₜ[R] exteriorPower.ιMulti R n
      (fun i => Finsupp.single (v i) 1)) = _
  exact CoordinateComplexIso.word R A σ n _ v

def pullback : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A ⟶ AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R B :=
  OrdinaryDeRhamFunctor.Ordinary.map (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B))

theorem pullback_coordinates (n : ℕ) (z : AlgebraicGeometry.Crystalline.Cohomology.Koszul.Tensor.KoszulTensor.Term R σ A n) :
    (pullback R A B).f n ((CoordinateComplexIso.iso R A σ).hom.f n z) =
      (CoordinateComplexIso.iso R B σ).hom.f n
        (TensorProduct.map (IsScalarTower.toAlgHom R A B).toLinearMap LinearMap.id z) := by
  have he : ((pullback R A B).f n).hom.comp
        ((CoordinateComplexIso.iso R A σ).hom.f n).hom =
      ((CoordinateComplexIso.iso R B σ).hom.f n).hom.comp
        (TensorProduct.map (IsScalarTower.toAlgHom R A B).toLinearMap LinearMap.id) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext_on (AlgebraicGeometry.Crystalline.Cohomology.ExteriorCoordinate.ExteriorCoordinateProjection.word_span R σ n)
    rintro _ ⟨v, rfl⟩
    change (pullback R A B).f n
      ((CoordinateComplexIso.iso R A σ).hom.f n
        (a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1))) = _
    rw [CoordinateComplexIso.word]
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A B)) n
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a (AlgebraicGeometry.Crystalline.Cohomology.EtaleCoordinate.EtaleCoordinateDerivations.coordinate R A σ ∘ v)) =
        (CoordinateComplexIso.iso R B σ).hom.f n
          (algebraMap A B a ⊗ₜ[R] exteriorPower.ιMulti R n (fun i => Finsupp.single (v i) 1))
    rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, CoordinateComplexIso.word]
    congr 1
    exact funext (fun i => coordinate_map R A B σ (v i))
  exact LinearMap.congr_fun he z

theorem pullback_trace :
    pullback R A B ≫ DeRhamTrace.trace R A B σ b =
      (Fintype.card ι : R) • 𝟙 (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((CoordinateComplexIso.iso R A σ).hom.f n)).mp inferInstance ω
  change (DeRhamTrace.trace R A B σ b).f n
    ((pullback R A B).f n ((CoordinateComplexIso.iso R A σ).hom.f n z)) =
      (Fintype.card ι : R) • (CoordinateComplexIso.iso R A σ).hom.f n z
  rw [pullback_coordinates R A B σ n z, trace_coordinates R A B σ b n]
  have ht : TensorProduct.map ((Algebra.trace A B).restrictScalars R) LinearMap.id
      (TensorProduct.map (IsScalarTower.toAlgHom R A B).toLinearMap LinearMap.id z) =
        (Fintype.card ι : R) • z := by
    induction z using TensorProduct.inductionOn with
    | tmul a η =>
      change Algebra.trace A B (algebraMap A B a) ⊗ₜ[R] η =
        (Fintype.card ι : R) • (a ⊗ₜ[R] η)
      rw [Algebra.trace_algebraMap_of_basis b, Nat.cast_smul_eq_nsmul,
        TensorProduct.smul_tmul']
    | add x y hx hy =>
      simp only [map_add, hx, hy]
      exact (smul_add (Fintype.card ι : R) x y).symm
  rw [ht]
  exact ((CoordinateComplexIso.iso R A σ).hom.f n).hom.map_smul _ _

theorem cohomology_pullback_trace (n : ℕ) :
    HomologicalComplex.homologyMap (pullback R A B) n ≫
        HomologicalComplex.homologyMap (DeRhamTrace.trace R A B σ b) n =
      (Fintype.card ι : R) • 𝟙 ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A).homology n) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℕ) n
  change H.map (pullback R A B) ≫ H.map (DeRhamTrace.trace R A B σ b) = _
  rw [← H.map_comp, pullback_trace, Nat.cast_smul_eq_nsmul, H.map_nsmul, H.map_id,
    Nat.cast_smul_eq_nsmul]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.DeRhamTrace
