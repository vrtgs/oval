pub struct FunctionItem {}

pub struct ConstItem {}

pub enum Item {
    Function(FunctionItem),
    Const(ConstItem),
}
