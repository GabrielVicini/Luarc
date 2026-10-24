local make = require("./class")
local other = make(12)
print("module", other:get(), other["x"])
local function read(t) return t.x end
local plain = {x = 4}
print("module-shared", read(other), read(plain), plain.get == nil)
