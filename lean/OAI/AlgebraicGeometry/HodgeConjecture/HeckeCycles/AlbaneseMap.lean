import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Models
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMapCompatibility
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TotalAlbaneseMap

/-! # Albanese Map -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMap.CM.Hecke

noncomputable section

/-! TateComparison's arithmetic Albanese map uses the original IntegralModel component
decomposition. The canonical coproduct assembly is proved equal to that
decomposition, so the total map is the same actual morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

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

variable (hg : (Models.CM.Hecke.data V D e C χ).HasIntegralModelGeometry)

theorem map_eq : AlbaneseMapCompatibility.CM.arithmeticMap (Models.CM.Hecke.data V D e C χ) hg =
    TotalAlbaneseMap.CM.map D e := by
  let : IsIso (Models.CM.Hecke.data V D e C χ).componentAssembly := hg.decomposition
  have he : asIso (Models.CM.Hecke.data V D e C χ).componentAssembly = e :=
    Iso.ext (Models.CM.Hecke.assembly_eq V D e C χ)
  exact congrArg (fun u : (∐ D.S) ≅ V.toOver =>
    D.totalMap u ≫ (AbelianScheme.TateComparison.Products.componentProductComparison D.A).inv) he

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlbaneseMap.CM.Hecke
