import SpectralStress.Basic
-- ρ_dom and ρ_rec have product 32, not 16.
example : SpectralStress.ρdom * SpectralStress.ρrec = 16 := by
  unfold SpectralStress.ρdom SpectralStress.ρrec; nlinarith [SpectralStress.sqrt2_sq]
