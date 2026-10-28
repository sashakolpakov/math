import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELModuli
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GenericIdentities

/-! # Models -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models.CM.Hecke

noncomputable section

/-! Assemble TateComparison's geometric input from the actual IntegralModel integral spread.
The correspondence covers remain separate: this module proves the complete
IntegralModel geometry predicate without assuming that predicate on the assembled data. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELModuli.CM

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s N : ℕ}
  {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K} {κ : K →+* ℂ}
  {M : Over (Spec (.of K))} {U : AbelianModuli.ReferenceFamily.PEL.Objects.PELObject P iota N M}
  {B : PELModuli.IntegralModel.Base.ArithmeticBaseExtension K κ}
  (V : PELModuli.IntegralModel.PEL.Has.IntegralPELSpread P iota κ N M U B)
  {r : ℕ} (D : PELModuli.IntegralModel.Components.ComponentAlbaneseData V.toOver r) (e : (∐ D.S) ≅ V.toOver)
  {q : ℕ} [Fact q.Prime]
  (C : AbelianScheme.TateComparison.Local.IntegralType s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback B.generic).obj V.toOver))
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

def data : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E B.extension.carrier s q where
  reference := P
  fieldEmbedding := (algebraMap K B.extension.carrier).comp iota
  complexEmbedding := B.embedding
  level := N
  denominator := B.denominator
  denominator_ne_zero := B.denominator_ne_zero
  model := PELModuli.CM.candidate V
  componentCount := r
  components := D
  inclusion j := Sigma.ι D.S j ≫ e.hom
  correspondence := C
  localCharacter := χ

theorem assembly_eq : (data V D e C χ).componentAssembly = e.hom := by
  apply Sigma.hom_ext
  intro j
  exact Sigma.ι_comp_desc (fun i => Sigma.ι D.S i ≫ e.hom) j

theorem integral_model_reduced (hV : Smooth V.toOver.hom) : IsReduced V.toOver.left := by
  let : Smooth V.toOver.hom := hV
  let : IsDomain B.R := Localization.Away.isDomain
    (Nat.cast_ne_zero.mpr B.denominator_ne_zero)
  let : GeometricallyReduced V.toOver.hom := PELModuli.IntegralModel.GenericIdentities.geometricallyReduced_of_smooth V.toOver.hom
  exact GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian V.toOver.hom

/-- Every geometric clause is supplied by IntegralModel, or derived from its
smoothness and the explicit component decomposition. -/
theorem geometry_from_integral
    (hP : P.IsAdmissible) (hEmb : κ.comp iota = P.μ)
    (hN : 3 ≤ N) (hunit : IsUnit (N : B.R))
    (hclassifies : V.IsReducedPELModuli P)
    (hsmooth : Smooth V.toOver.hom) (hproper : IsProper V.toOver.hom)
    (hprojective : PELModuli.IntegralModel.Components.RelativelyProjective V.toOver)
    (hcomponents : ∀ j : Fin r,
      Smooth (D.S j).hom ∧ IsProper (D.S j).hom ∧
      PELModuli.IntegralModel.Components.RelativelyProjective (D.S j) ∧ GeometricallyConnected (D.S j).hom ∧
      Smooth (D.A j).X.hom ∧ IsProper (D.A j).X.hom ∧
      GeometricallyConnected (D.A j).X.hom ∧ D.IsComplexAlbanese B.complexPoint j)
    (hbetti : Function.Bijective (PELModuli.IntegralModel.Product.bettiPullbackQ (D.totalComplexMap B.complexPoint e) 1))
    (hgeneration : ∀ j : Fin r, ∃ n : ℕ, 0 < n ∧
      ∀ t : PELModuli.IntegralModel.Base.GeometricPoint B.base, Function.Surjective (D.sumOfDifferences j n t)) :
    (data V D e C χ).HasIntegralModelGeometry := by
  let Q := data V D e C χ
  have hassembly : Q.componentAssembly = e.hom := assembly_eq V D e C χ
  have hdecomp : IsIso Q.componentAssembly :=
    hassembly.symm ▸ (inferInstanceAs (IsIso e.hom))
  refine {
    reference_admissible := hP
    embedding := ?_
    fullLevel := hN
    levelUnit := hunit
    classifies := PELModuli.CM.classifiesReduced_from_integral V hclassifies
    reduced := integral_model_reduced V hsmooth
    smooth := hsmooth
    proper := hproper
    projective := hprojective
    decomposition := hdecomp
    componentGeometry := fun j => ⟨(hcomponents j).1, (hcomponents j).2.1,
      (hcomponents j).2.2.1, (hcomponents j).2.2.2.1⟩
    abelianGeometry := fun j => ⟨(hcomponents j).2.2.2.2.1,
      (hcomponents j).2.2.2.2.2.1, (hcomponents j).2.2.2.2.2.2.1⟩
    albanese := fun j => (hcomponents j).2.2.2.2.2.2.2
    betti := ?_
    generation := hgeneration }
  · change B.embedding.comp ((algebraMap K B.extension.carrier).comp iota) = P.μ
    rw [← RingHom.comp_assoc, B.embedding_extends, hEmb]
  · let : IsIso Q.componentAssembly := hdecomp
    have he : asIso Q.componentAssembly = e := Iso.ext hassembly
    exact (congrArg (fun e' : (∐ D.S) ≅ V.toOver => Function.Bijective
      (PELModuli.IntegralModel.Product.bettiPullbackQ (D.totalComplexMap B.complexPoint e') 1)) he).mpr hbetti

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models.CM.Hecke
