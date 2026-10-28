import OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicNaturality

/-! # Logarithmic Frame -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicFrame.Forms

noncomputable section

/-! Logarithmic coordinate products from two different PD algebras
agree modulo an explicit boundary in a common PD target whenever
their images have the same residue. The maps are the original PD
de Rham pullbacks. -/
open _root_.CategoryTheory
universe u
variable {R : Type u} [CommRing R]
  {A B C : CommAlgCat.{u} R}
  {I : Ideal A} {δI : DividedPowers I}
  {J : Ideal B} {δJ : DividedPowers J}
  {K : Ideal C} {δK : DividedPowers K}

theorem formMap_logarithmicWedge (f : A ⟶ C)
    (hf : DividedPowers.IsDPMorphism δI δK f.hom.toRingHom)
    (n : ℕ) (v : Fin n → Aˣ) :
    AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf n (LogarithmicWedges.Forms.logarithmicWedge R A I δI n v) =
      LogarithmicWedges.Forms.logarithmicWedge R C K δK n (fun i => Units.map f.hom.toMonoidHom (v i)) :=
  LogarithmicNaturality.Forms.addMap_logarithmicWedge R R A C I δI K δK f.hom.toRingHom
    (fun j => (AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf j).toAddMonoidHom)
    (fun j a v => AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap_symbol f hf j a v) n v

theorem commonFrame_exact (f : A ⟶ C) (g : B ⟶ C)
    (hf : DividedPowers.IsDPMorphism δI δK f.hom.toRingHom)
    (hg : DividedPowers.IsDPMorphism δJ δK g.hom.toRingHom)
    (p r : ℕ) (hp : 0 < p) (hpr : (p : C) ^ r = 0)
    (n : ℕ) (u : Fin (n + 1) → Aˣ) (v : Fin (n + 1) → Bˣ)
    (huv : ∀ i, g (v i : B) - f (u i : A) ∈ K) :
    ∃ η : AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.Form R C K δK n,
      AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap g hg (n + 1) (LogarithmicWedges.Forms.logarithmicWedge R B J δJ (n + 1) v) -
        AlgebraicGeometry.Crystalline.Cohomology.PD.DeRhamGlobal.PDDeRhamGlobal.formMap f hf (n + 1) (LogarithmicWedges.Forms.logarithmicWedge R A I δI (n + 1) u) =
          AlgebraicGeometry.Crystalline.Cohomology.PD.DeRham.PDDeRham.differential R C K δK n η := by
  rw [formMap_logarithmicWedge g hg, formMap_logarithmicWedge f hf]
  apply LogarithmicWedges.Forms.congruent_wedges_exact R C K δK p r hp hpr n
    (fun i => Units.map f.hom.toMonoidHom (u i))
    (fun i => Units.map g.hom.toMonoidHom (v i))
  intro i
  exact huv i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.PD.LogarithmicFrame.Forms
