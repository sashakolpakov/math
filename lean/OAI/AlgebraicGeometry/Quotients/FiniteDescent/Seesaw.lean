import OAI.AlgebraicGeometry.Quotients.FiniteDescent.OpenCounit

/-! # Seesaw -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.Seesaw.Construction.SeesawDescent

noncomputable section

/-! The seesaw descent step: local frames over the base and a trivial
restriction to a section give one global frame. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
variable (hO : ∀ U : S.Opens,
  IsIso (SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom))
variable (hn : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ Nonempty
  ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (f ⁻¹ᵁ U).toScheme))

def trivial (s : S ⟶ X) (hs : s ≫ f = 𝟙 _)
    (e : (Scheme.Modules.pullback s).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S) : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X := by
  have := OpenCounit.Construction.OpenCounitDescent.counit f M hO hn
  let N := (Scheme.Modules.pushforward f).obj M
  let c : (Scheme.Modules.pullback f).obj N ≅ M :=
    asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M)
  let q : (Scheme.Modules.pullback s).obj ((Scheme.Modules.pullback f).obj N) ≅ N :=
    (Scheme.Modules.pullbackComp s f).app N ≪≫
      (Scheme.Modules.pullbackCongr hs).app N ≪≫ (Scheme.Modules.pullbackId S).app N
  let n : N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule S := q.symm ≪≫ (Scheme.Modules.pullback s).mapIso c ≪≫ e
  exact c.symm ≪≫ (Scheme.Modules.pullback f).mapIso n ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.Seesaw.Construction.SeesawDescent
