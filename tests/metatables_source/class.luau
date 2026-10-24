local C = {}
C.__index = C
function C:get() return self.x end
return function(x) return setmetatable({x = x}, C) end
