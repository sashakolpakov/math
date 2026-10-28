import Mathlib.AlgebraicGeometry.Noetherian
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.KoszulGermSupport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleStalk
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Regular.LocalNegativeCochainExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.ComplexLocalExactness

/-! # Mixed Koszul Stalk Exactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulStalkExactness

noncomputable section

/-! A framed mixed Koszul complex with finitely many common zeros
is exact in negative degrees at an actual regular stalk of the matching
dimension. Both its local equations and its local module structure are
constructed from the original sheaves. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry IsLocalRing
universe u

theorem framedMixedKoszul_stalk_exact_negative
    {X : Scheme.{u}} [JacobsonSpace X] [IsLocallyNoetherian X]
    (x : X) (M : X.Modules) (eM : M ≅ Line.Bundles.structureModule X)
    (bs : List (LineBundleKoszulComplex.LineBundleSection X))
    (frames : ∀ b ∈ bs, Nonempty (b.1.sheaf ≅ Line.Bundles.structureModule X))
    (hfinite : (MixedKoszulGeometricSupport.mixedSectionZeroSet bs).Finite)
    (ps : List (X.presheaf.stalk x)) (hlen : bs.length = ps.length)
    (hreg : Regular.SequenceBasic.RingTheory.Sequence.IsRegular (X.presheaf.stalk x) ps)
    (hgen : Regular.SequenceBasic.Ideal.ofList ps = maximalIdeal (X.presheaf.stalk x)) :
    ∀ i : ℤ, i < 0 →
      (((HilbertConstruction.Module.StalkExactness.moduleStalkFunctor x).mapHomologicalComplex (.up ℤ)).obj
        (LineBundleKoszulComplex.mixedLineBundleKoszulComplex M bs)).ExactAt i := by
  classical
  let R := X.presheaf.stalk x
  let F := HilbertConstruction.Module.StalkExactness.moduleStalkFunctor x
  let φ : Γ(X, ⊤) →+* R := (X.presheaf.germ ⊤ x trivial).hom
  let ρ : LineBundleKoszulComplex.LineBundleSection X → R := fun b =>
    if hb : b ∈ bs then φ (Frame.Coordinates.structureModuleEndValue X (b.2 ≫ (Classical.choice (frames b hb)).hom)) else 0
  have hρ : ∀ b ∈ bs, ∃ e : b.1.sheaf ≅ Line.Bundles.structureModule X,
      φ (Frame.Coordinates.structureModuleEndValue X (b.2 ≫ e.hom)) = ρ b := by
    intro b hb
    exact ⟨Classical.choice (frames b hb), by simp only [ρ, dite_eq_left hb]⟩
  let V := F.obj M
  let eV : V ≅ ModuleCat.of R R := F.mapIso eM ≪≫ Structure.ModuleStalk.structureModuleStalkIso x
  have : Module.Finite R V := Module.Finite.equiv eV.symm.toLinearEquiv
  have : Module.Free R V := Module.Free.of_equiv eV.symm.toLinearEquiv
  let rs := bs.map ρ
  let C := ScalarKoszul.KoszulComplex.scalarKoszulComplex V rs
  have hff := ScalarKoszul.FiniteTerms.scalarKoszulComplex_finite_free V rs
  have hlength : rs.length = ps.length := by simpa only [rs, List.length_map] using hlen
  have hsupport := KoszulGermSupport.framedKoszul_germ_support_closedPoint x bs hfinite ρ hρ
  have hexa : ∀ i : ℤ, i < 0 → C.ExactAt i := by
    refine Regular.LocalNegativeCochainExactness.regularLocal_negative_cochain_exact C ps.length
      (fun i => (hff i).1) (fun i => (hff i).2) ?_ ps rfl hreg hgen ?_
    · intro i hi
      exact ScalarKoszul.KoszulComplex.scalarKoszulComplex_isZero_X V rs i (Or.inl (by simpa only [hlength] using hi))
    · intro B _ _ hnot
      have hnotI : ¬ Regular.SequenceBasic.Ideal.ofList rs ≤ RingHom.ker (algebraMap R B) := by
        intro hI
        let P : PrimeSpectrum R := ⟨RingHom.ker (algebraMap R B), RingHom.ker_isPrime _⟩
        have hP : P ∈ PrimeSpectrum.zeroLocus (Regular.SequenceBasic.Ideal.ofList rs : Set R) := hI
        have he : P = IsLocalRing.closedPoint R := hsupport hP
        have heI : RingHom.ker (algebraMap R B) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal he
        exact hnot heI.symm.le
      exact HilbertConstruction.Module.ComplexLocalExactness.cochain_acyclic_of_contractible _
        (ScalarKoszul.KoszulComplex.scalarKoszulComplex_field_contractible_off_ideal B V rs hnotI)
  let e := MixedKoszulFunctor.framedMixedKoszulFunctorIso F φ (Structure.ModuleStalk.moduleStalkFunctor_globalScalar x) M bs ρ hρ
  intro i hi
  exact (exactAt_iff_of_quasiIsoAt e.hom i).mpr (hexa i hi)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.MixedKoszulStalkExactness
