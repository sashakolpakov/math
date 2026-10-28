import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover

/-! # Integer Generator -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerGenerator.IntegerGeneratorDetection

noncomputable section

/-! A map out of the actual integer constant sheaf is detected by its generator on a covering object. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian _root_.AlgebraicGeometry Opposite

universe u
variable {X : Scheme.{u}} {F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}

theorem section_eq_zero_of_cover {U V : X.ProEt} (g : U ⟶ V)
    [Surjective g.left] [QuasiCompact g.left] (s : F.obj.obj (op V))
    (hs : F.obj.map g.op s = 0) : s = 0 := by
  let G := (sheafCompose _ (forget Ab.{u + 1})).obj F
  have hG := (isSheaf_iff_isSheaf_of_type _ _).mp G.property
  apply (hG.isSheafFor _ (AlgebraicGeometry.FormalGeometry.Completion.ProEtale.SingleCover.Construction.proEtaleSingleton_cover g)).isSeparatedFor.ext
  intro W f hf
  cases hf
  exact hs.trans ((F.obj.map g.op).hom.map_zero).symm

theorem hom_eq_zero_of_cover {U : X.ProEt} (g : U ⟶ ⊤_ X.ProEt)
    [Surjective g.left] [QuasiCompact g.left] (f : AlgebraicGeometry.FormalGeometry.Completion.ProetalePullback.Construction.proEtIntegerConstant X ⟶ F)
    (hf : f.hom.app (op U) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U) = 0) : f = 0 := by
  have ht : f.hom.app (op (⊤_ X.ProEt)) (AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.App.Construction.proEtIntegerGenerator X) = 0 := by
    apply section_eq_zero_of_cover g
    rw [← NatTrans.naturality_apply]
    have hg : g = terminal.from U := terminalIsTerminal.hom_ext _ _
    rw [hg]
    exact hf
  apply (Ext.mk₀_bijective _ _).injective
  apply (Sheaf.H.equiv₀ F terminalIsTerminal).injective
  have h := Sheaf.H.equiv₀_naturality (f := f) terminalIsTerminal (Ext.mk₀ (𝟙 _))
  simp only [Sheaf.H.map_apply, Ext.mk₀_id_comp] at h
  rw [← h, Ext.mk₀_zero, map_zero]
  exact ht

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegerGenerator.IntegerGeneratorDetection
