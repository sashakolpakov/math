import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport

/-! # Complex Transport Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality

noncomputable section

/-!
# IntegralComparison: augmentation transport commutes with maps of the target complex
-/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
  {Z : C} {Z' : D} (e : F.obj Z ≅ Z')
  {K L : CochainComplex C ℕ} (ι : (CochainComplex.single₀ C).obj Z ⟶ K) (a : K ⟶ L)

theorem comp : ComplexTransport.map F e ι ≫
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map a =
      ComplexTransport.map F e (ι ≫ a) := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℕ)
  exact (Category.assoc (ComplexTransport.sourceIso F e).inv (G.map ι) (G.map a)).trans
    (congrArg (fun b => (ComplexTransport.sourceIso F e).inv ≫ b) (G.map_comp ι a).symm)

omit a in
theorem quasiIso [F.PreservesHomology] [QuasiIso ι] : QuasiIso (ComplexTransport.map F e ι) := by
  dsimp only [ComplexTransport.map]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransportNaturality
