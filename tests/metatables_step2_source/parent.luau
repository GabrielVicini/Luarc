local Parent = {}
function Parent.new(x) return setmetatable({x = x}, {__index = Parent}) end
function Parent:get() return self.x end
return Parent
