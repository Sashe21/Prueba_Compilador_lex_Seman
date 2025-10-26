"""
COMPILADOR COMPLETO PF2024 - AUTOMATAS 2
Incluye todas las fases del compilador:
- Análisis Léxico
- Análisis Sintáctico  
- Análisis Semántico
- Generación de Código Intermedio
- Generación de Código Ensamblador
"""

import ply.lex as lex
import ply.yacc as yacc
import tkinter as tk
from tkinter import scrolledtext, ttk, filedialog, messagebox

# ================= DEFINICIÓN DE TOKENS =================
tokens = (
    'PROG','TIPO','TIPO_INT','TIPO_CAD','TIPO_BOOL', 'DECL', 'INICIO', 'FIN',
    'LEERDIG', 'IMPDIG', 'LEERCAD', 'IMPCAD',
    'LEERBOOL', 'IMPBOOL', 'FALS', 'VERD', 'SI',
    'SINO', 'PARA', 'MIENTRAS', 'UNION', 'INTER',
    'IN', 'OR', 'AND', 'NOT', 'PC', 'COMA', 'MAS',
    'MENOS', 'MUL', 'DIV', 'ASIG', 'PAREN', 'TESIS',
    'SIGMENOR', 'SIGMAYOR', 'IGUAL', 'SIGDIF',
    'ID', 'CINT', 'ERROR', 'CAD', 'ERROR_IDENTIFICADOR', 'ERROR_IDENTIFICADOR_SIM'
)

# Diccionario de palabras reservadas
reservadas = {
    'pf2024': ('PROG', 0),
    'Inicio': ('INICIO', 5),
    'Fin': ('FIN', 6),
    'Int': ('TIPO_INT', 1),
    'decl': ('DECL', 4),
    'Cad': ('TIPO_CAD', 2),
    'Bool': ('TIPO_BOOL', 3),
    'leerdig': ('LEERDIG', 7),
    'impdig': ('IMPDIG', 8),
    'Leercad': ('LEERCAD', 9),
    'impcad': ('IMPCAD', 10),
    'leerbol': ('LEERBOOL', 11),
    'Impbool': ('IMPBOOL', 12),
    'falso': ('FALS', 13),
    'verdadero': ('VERD', 14),
    'si': ('SI', 15),
    'sino': ('SINO', 16),
    'para': ('PARA', 17),
    'mientras': ('MIENTRAS', 18),
    'union': ('UNION', 19),
    'inter': ('INTER', 20),
    'in': ('IN', 21),
    'or': ('OR', 22),
    'and': ('AND', 23),
    'not': ('NOT', 24)
}

# ================= TOKENS SIMPLES =================
t_PC = r';'
t_COMA = r','
t_MAS = r'\+'
t_MENOS = r'-'
t_MUL = r'\*'
t_DIV = r'/'
t_ASIG = r':='
t_PAREN = r'\('
t_TESIS = r'\)'
t_SIGMENOR = r'<'
t_SIGMAYOR = r'>'
t_IGUAL = r'='
t_SIGDIF = r'<>'

# ================= VARIABLES GLOBALES =================
errores = []
errores_semanticos = []
tabla_simbolos = []
contador_simbolos = 1
arboles_operaciones = []
t_ignore = ' \t'
lineas_codigo = []
tabla_tipos = {}
temp_counter = 0
label_counter = 0
cuadruplos_globales = []
codigo_intermedio = []

# ================= CLASES PARA ANÁLISIS SEMÁNTICO =================

class ErrorSemantico:
    """Representa un error semántico encontrado durante el análisis"""
    def __init__(self, linea, tipo, descripcion, contexto, sugerencia=None):
        self.linea = linea
        self.tipo = tipo
        self.descripcion = descripcion
        self.contexto = contexto
        self.sugerencia = sugerencia

class Variable:
    """Representa una variable declarada en el programa"""
    def __init__(self, nombre, tipo, linea_declaracion, inicializada=False):
        self.nombre = nombre
        self.tipo = tipo
        self.linea_declaracion = linea_declaracion
        self.inicializada = inicializada
        self.usada = False
        self.lineas_uso = []
        self.valor = None

class AnalizadorSemantico:
    """Realiza el análisis semántico del código fuente"""
    def __init__(self):
        self.variables = {}
        self.variables_declaradas = set()
        self.variables_utilizadas = set()
        self.en_declaracion = False
        self.tipo_actual = None
        self.linea_actual = 1
        
    def reiniciar(self):
        """Reinicia el estado del analizador semántico"""
        self.variables = {}
        self.variables_declaradas = set()
        self.variables_utilizadas = set()
        self.en_declaracion = False
        self.tipo_actual = None
        self.linea_actual = 1

    def declarar_variable(self, nombre, tipo, linea):
        """Declara una nueva variable y verifica duplicados"""
        if nombre in self.variables:
            error = ErrorSemantico(
                linea=linea,
                tipo="VARIABLE_DUPLICADA",
                descripcion=f"La variable '{nombre}' ya fue declarada anteriormente",
                contexto=f"Primera declaración en línea {self.variables[nombre].linea_declaracion}",
                sugerencia=f"Use un nombre diferente o elimine la declaración duplicada"
            )
            errores_semanticos.append(error)
        else:
            self.variables[nombre] = Variable(nombre, tipo, linea)
            self.variables_declaradas.add(nombre)
    
    def usar_variable(self, nombre, linea):
        """Registra el uso de una variable y verifica que esté declarada"""
        if nombre not in self.variables:
            error = ErrorSemantico(
                linea=linea,
                tipo="VARIABLE_NO_DECLARADA",
                descripcion=f"La variable '{nombre}' no ha sido declarada",
                contexto=f"Se intenta usar '{nombre}' sin declaración previa",
                sugerencia=f"Declare la variable '{nombre}' en la sección 'decl' antes de usarla"
            )
            errores_semanticos.append(error)
            return None
        else:
            self.variables[nombre].usada = True
            self.variables[nombre].lineas_uso.append(linea)
            self.variables_utilizadas.add(nombre)
            return self.variables[nombre]
    
    def asignar_variable(self, nombre, tipo_expresion, linea):
        """Registra una asignación y verifica compatibilidad de tipos"""
        variable = self.usar_variable(nombre, linea)
        if variable:
            if tipo_expresion and variable.tipo != tipo_expresion:
                error = ErrorSemantico(
                    linea=linea,
                    tipo="INCOMPATIBILIDAD_TIPOS",
                    descripcion=f"Incompatibilidad de tipos en asignación",
                    contexto=f"Se intenta asignar tipo '{tipo_expresion}' a variable '{nombre}' de tipo '{variable.tipo}'",
                    sugerencia=f"Verifique que la expresión sea compatible con el tipo '{variable.tipo}'"
                )
                errores_semanticos.append(error)
            variable.inicializada = True
    
    def verificar_operacion_aritmetica(self, operandos, operador, linea):
        """Verifica que los operandos de una operación aritmética sean del tipo correcto"""
        tipo_esperado = "Int"
        for operando in operandos:
            if isinstance(operando, str) and operando in self.variables:
                variable = self.variables[operando]
                if variable.tipo != tipo_esperado:
                    error = ErrorSemantico(
                        linea=linea,
                        tipo="OPERACION_TIPO_INVALIDO",
                        descripcion=f"Operación aritmética '{operador}' no válida para tipo '{variable.tipo}'",
                        contexto=f"Variable '{operando}' de tipo '{variable.tipo}' en operación aritmética",
                        sugerencia=f"Use variables de tipo '{tipo_esperado}' en operaciones aritméticas"
                    )
                    errores_semanticos.append(error)
    
    def verificar_variables_no_utilizadas(self):
        """Verifica si hay variables declaradas pero no utilizadas"""
        for nombre, variable in self.variables.items():
            if not variable.usada:
                error = ErrorSemantico(
                    linea=variable.linea_declaracion,
                    tipo="VARIABLE_NO_UTILIZADA",
                    descripcion=f"La variable '{nombre}' fue declarada pero nunca utilizada",
                    contexto=f"Variable '{nombre}' de tipo '{variable.tipo}' declarada en línea {variable.linea_declaracion}",
                    sugerencia=f"Elimine la declaración de '{nombre}' si no la necesita, o úsela en el código"
                )
                errores_semanticos.append(error)
    
    def verificar_variables_no_inicializadas(self):
        """Verifica si hay variables usadas sin inicializar"""
        for nombre, variable in self.variables.items():
            if variable.usada and not variable.inicializada:
                error = ErrorSemantico(
                    linea=variable.lineas_uso[0] if variable.lineas_uso else variable.linea_declaracion,
                    tipo="VARIABLE_NO_INICIALIZADA",
                    descripcion=f"La variable '{nombre}' se usa sin haber sido inicializada",
                    contexto=f"Variable '{nombre}' usada en líneas {variable.lineas_uso} sin asignación previa",
                    sugerencia=f"Asigne un valor a '{nombre}' antes de usarla"
                )
                errores_semanticos.append(error)

analizador_sem = AnalizadorSemantico()

# ================= CLASES AUXILIARES =================
class NodoOperacion:
    """Representa un nodo en el árbol de sintaxis abstracta"""
    def __init__(self, tipo, valor=None, izquierdo=None, derecho=None, linea=None):
        self.tipo = tipo
        self.valor = valor
        self.izquierdo = izquierdo
        self.derecho = derecho
        self.linea = linea or 1
        self.tipo_dato = None

class SimboloTabla:
    """Representa un símbolo en la tabla de símbolos"""
    def __init__(self, lexema, token, referencia=None):
        global contador_simbolos
        self.numero = contador_simbolos
        self.lexema = lexema
        self.token = token
        self.referencia = referencia
        contador_simbolos += 1

# ================= FUNCIONES AUXILIARES =================
def agregar_simbolo(lexema, token, referencia=None):
    """Agrega un símbolo a la tabla de símbolos si no existe"""
    for simbolo in tabla_simbolos:
        if simbolo.lexema == lexema and simbolo.token == token:
            return simbolo
    nuevo_simbolo = SimboloTabla(lexema, token, referencia)
    tabla_simbolos.append(nuevo_simbolo)
    return nuevo_simbolo

def reiniciar_datos():
    """Reinicia todas las estructuras de datos globales"""
    global errores, errores_semanticos, tabla_simbolos, contador_simbolos, arboles_operaciones
    global lineas_codigo, tabla_tipos, temp_counter, label_counter, cuadruplos_globales, codigo_intermedio
    errores = []
    errores_semanticos = []
    tabla_simbolos = []
    contador_simbolos = 1
    arboles_operaciones = []
    lineas_codigo = []
    tabla_tipos = {}
    temp_counter = 0
    label_counter = 0
    cuadruplos_globales = []
    codigo_intermedio = []
    analizador_sem.reiniciar()

def obtener_linea_actual(p):
    """Obtiene el número de línea actual del parser"""
    try:
        if hasattr(p, 'lineno'):
            if hasattr(p.lineno, '__call__'):
                return p.lineno(1) if len(p) > 1 else 1
            else:
                return p.lineno
        elif len(p) > 1 and hasattr(p.slice[1], 'lineno'):
            return p.slice[1].lineno
        else:
            return 1
    except (AttributeError, IndexError):
        return 1

def nuevo_temp():
    """Genera un nuevo nombre de variable temporal"""
    global temp_counter
    temp_counter += 1
    return f"t{temp_counter}"

def nueva_etiqueta():
    """Genera una nueva etiqueta para saltos"""
    global label_counter
    label_counter += 1
    return f"L{label_counter}"

# ================= FUNCIONES DE TOKENS (ANALIZADOR LÉXICO) =================

def t_CINT(tok):
    r'\d+'
    tok.value = int(tok.value)
    return tok

def t_CAD(tok):
    r'"[^"]*"'
    return tok

def t_ID(t):
    r'[a-zA-Z][a-zA-Z0-9_]*'
    if t.value in reservadas:
        token_info = reservadas[t.value]
        t.type = token_info[0]
        t.ref = token_info[1]
    else:
        t.type = 'ID'
        t.ref = None
    return t

def t_ERROR_IDENTIFICADOR_NUM(t):
    r'\d+[a-zA-Z_]+[a-zA-Z0-9_]*'
    t.type = 'ERROR'
    errores.append({
        'line': t.lineno,
        'value': t.value,
        'type': 'ERROR_IDENTIFICADOR',
        'desc': 'Los identificadores no pueden empezar con números'
    })
    return t

def t_ERROR_IDENTIFICADOR(t):
    r'[a-zA-Z_][a-zA-Z0-9_]*[#$%&!]+[a-zA-Z0-9_]*|[a-zA-Z_]*[#$%&!]+[a-zA-Z0-9_]*'
    t.type = 'ERROR'
    errores.append({
        'line': t.lineno,
        'value': t.value,
        'type': 'ERROR_IDENTIFICADOR',
        'desc': 'Los identificadores solo pueden contener letras, números y guiones bajos'
    })
    return t

def t_newline(tok):
    r'\n+'
    tok.lexer.lineno += len(tok.value)

def t_COMENTARIO(tok):
    r'/\*[^*]*\*+(?:[^/*][^*]*\*+)*/|//.*'
    tok.lexer.lineno += tok.value.count('\n')
    pass

def t_error(t):
    """Maneja errores léxicos"""
    errores.append({
        'line': t.lineno,
        'value': t.value[0],
        'type': 'ERROR_LEXICO',
        'desc': f'Carácter ilegal "{t.value[0]}"'
    })
    t.lexer.skip(1)

analizador_lexico = lex.lex()

# ================= ANALIZADOR SINTÁCTICO =================

precedence = (
    ('left', 'MAS', 'MENOS'),
    ('left', 'MUL', 'DIV'),
    ('right', 'UMINUS'),
)

# ================= REGLAS GRAMATICALES =================

def p_programa(p):
    '''programa : PROG ID programa_decl'''
    agregar_simbolo(p[1], 'PROG', 'Palabra clave del programa')
    agregar_simbolo(p[2], 'ID', 'Nombre del programa')
    analizador_sem.verificar_variables_no_utilizadas()
    analizador_sem.verificar_variables_no_inicializadas()

def p_programa_decl(p):
    '''programa_decl : declaraciones cuerpo_programa
                    | cuerpo_programa'''
    pass

def p_declaraciones(p):
    '''declaraciones : DECL lista_declaraciones'''
    agregar_simbolo(p[1], 'DECL', 'Sección de declaraciones')

def p_lista_declaraciones(p):
    '''lista_declaraciones : declaracion lista_declaraciones
                          | declaracion'''
    pass

def p_declaracion(p):
    '''declaracion : tipo lista_variables PC'''
    agregar_simbolo(';', 'PC', 'Fin de declaración')

def p_tipo(p):
    '''tipo : TIPO_INT
           | TIPO_CAD
           | TIPO_BOOL'''
    if p[1] == 'Int':
        agregar_simbolo('Int', 'TIPO_INT', 'Tipo de dato entero')
        analizador_sem.tipo_actual = 'Int'
    elif p[1] == 'Cad':
        agregar_simbolo('Cad', 'TIPO_CAD', 'Tipo de dato cadena')
        analizador_sem.tipo_actual = 'Cad'
    elif p[1] == 'Bool':
        agregar_simbolo('Bool', 'TIPO_BOOL', 'Tipo de dato booleano')
        analizador_sem.tipo_actual = 'Bool'

def p_lista_variables(p):
    '''lista_variables : ID COMA lista_variables
                      | ID'''
    linea = obtener_linea_actual(p)
    
    if len(p) == 2:
        agregar_simbolo(p[1], 'ID', 'Variable')
        analizador_sem.declarar_variable(p[1], analizador_sem.tipo_actual, linea)
    else:
        agregar_simbolo(p[1], 'ID', 'Variable')
        agregar_simbolo(',', 'COMA', 'Separador de variables')
        analizador_sem.declarar_variable(p[1], analizador_sem.tipo_actual, linea)

def p_cuerpo_programa(p):
    '''cuerpo_programa : INICIO instrucciones FIN'''
    agregar_simbolo('Inicio', 'INICIO', 'Inicio del programa')
    agregar_simbolo('Fin', 'FIN', 'Fin del programa')

def p_instrucciones(p):
    '''instrucciones : instruccion instrucciones
                    | instruccion'''
    pass

def p_instruccion(p):
    '''instruccion : asignacion
                  | llamada_funcion
                  | estructura_control'''
    pass

def p_estructura_control(p):
    '''estructura_control : si_entonces
                         | mientras_hacer
                         | para_hacer'''
    pass

def p_si_entonces(p):
    '''si_entonces : SI PAREN expresion TESIS instruccion
                  | SI PAREN expresion TESIS instruccion SINO instruccion'''
    linea = obtener_linea_actual(p)
    agregar_simbolo('si', 'SI', 'Estructura condicional')
    
    # Generar etiquetas para saltos
    etiq_falso = nueva_etiqueta()
    etiq_fin = nueva_etiqueta()
    
    # Evaluar condición y saltar si es falsa
    cuadruplos_globales.append(('if_false', p[3], None, etiq_falso))
    
    if len(p) == 6:  # Solo if
        cuadruplos_globales.append(('goto', None, None, etiq_fin))
        cuadruplos_globales.append(('label', None, None, etiq_falso))
    else:  # if-else
        cuadruplos_globales.append(('goto', None, None, etiq_fin))
        cuadruplos_globales.append(('label', None, None, etiq_falso))
        # Código del else
        cuadruplos_globales.append(('label', None, None, etiq_fin))

def p_mientras_hacer(p):
    '''mientras_hacer : MIENTRAS PAREN expresion TESIS instruccion'''
    agregar_simbolo('mientras', 'MIENTRAS', 'Estructura de repetición')
    
    etiq_inicio = nueva_etiqueta()
    etiq_fin = nueva_etiqueta()
    
    cuadruplos_globales.append(('label', None, None, etiq_inicio))
    cuadruplos_globales.append(('if_false', p[3], None, etiq_fin))
    # Código del cuerpo
    cuadruplos_globales.append(('goto', None, None, etiq_inicio))
    cuadruplos_globales.append(('label', None, None, etiq_fin))

def p_para_hacer(p):
    '''para_hacer : PARA PAREN asignacion expresion PC expresion TESIS instruccion'''
    agregar_simbolo('para', 'PARA', 'Estructura de repetición')
    
    etiq_inicio = nueva_etiqueta()
    etiq_fin = nueva_etiqueta()
    
    # Inicialización ya está en cuádruplos
    cuadruplos_globales.append(('label', None, None, etiq_inicio))
    cuadruplos_globales.append(('if_false', p[4], None, etiq_fin))
    # Código del cuerpo
    # Incremento
    cuadruplos_globales.append(('goto', None, None, etiq_inicio))
    cuadruplos_globales.append(('label', None, None, etiq_fin))

def p_asignacion(p):
    '''asignacion : ID ASIG expresion PC'''
    linea = obtener_linea_actual(p)
    
    agregar_simbolo(p[1], 'ID', 'Variable en asignación')
    agregar_simbolo(':=', 'ASIG', 'Operador de asignación')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')
    
    tipo_expresion = None
    if p[3]:
        tipo_expresion = getattr(p[3], 'tipo_dato', 'Int')
    
    analizador_sem.asignar_variable(p[1], tipo_expresion, linea)
    
    if p[3] and hasattr(p[3], 'tipo') and p[3].tipo in ['operacion', 'termino', 'ID']:
        valor, tipo_eval = evaluar_nodo(p[3])
        var = analizador_sem.variables.get(p[1])
        if valor is not None and var is not None:
            var.valor = valor
            var.inicializada = True

        resultado_operando, quads = generar_cuadruplos_desde_nodo(p[3], [])

        asign_dest = p[1]
        if resultado_operando is not None:
            quads.append((':=', resultado_operando, None, asign_dest))

        cuadruplos_globales.extend(quads)

        arboles_operaciones.append({
            'variable': p[1],
            'expresion': p[3],
            'linea': linea,
            'resultado': valor,
            'tipo_resultado': tipo_eval,
            'cuadruplos': quads
        })

def p_expresion_binaria(p):
    '''expresion : expresion MAS expresion
                | expresion MENOS expresion
                | expresion MUL expresion
                | expresion DIV expresion'''
    linea = obtener_linea_actual(p)
    
    operandos = []
    if hasattr(p[1], 'valor') and isinstance(p[1].valor, str):
        operandos.append(p[1].valor)
    if hasattr(p[3], 'valor') and isinstance(p[3].valor, str):
        operandos.append(p[3].valor)
    
    analizador_sem.verificar_operacion_aritmetica(operandos, p[2], linea)
    
    if p[2] == '+':
        agregar_simbolo('+', 'MAS', 'Operador suma')
        p[0] = NodoOperacion('operacion', '+', p[1], p[3], linea)
    elif p[2] == '-':
        agregar_simbolo('-', 'MENOS', 'Operador resta')
        p[0] = NodoOperacion('operacion', '-', p[1], p[3], linea)
    elif p[2] == '*':
        agregar_simbolo('*', 'MUL', 'Operador multiplicación')
        p[0] = NodoOperacion('operacion', '*', p[1], p[3], linea)
    elif p[2] == '/':
        agregar_simbolo('/', 'DIV', 'Operador división')
        p[0] = NodoOperacion('operacion', '/', p[1], p[3], linea)
        
        if hasattr(p[3], 'valor') and p[3].valor == '0':
            error = ErrorSemantico(
                linea=linea,
                tipo="DIVISION_POR_CERO",
                descripcion="Posible división por cero",
                contexto=f"División por constante cero en línea {linea}",
                sugerencia="Verifique que el divisor no sea cero"
            )
            errores_semanticos.append(error)
    
    p[0].tipo_dato = 'Int'

def p_expresion_unaria(p):
    '''expresion : MENOS expresion %prec UMINUS'''
    linea = obtener_linea_actual(p)
    agregar_simbolo('-', 'MENOS', 'Operador menos unario')
    p[0] = NodoOperacion('operacion', '-', None, p[2], linea)
    p[0].tipo_dato = 'Int'

def p_expresion_parentesis(p):
    '''expresion : PAREN expresion TESIS'''
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    p[0] = p[2]

def p_expresion_factor(p):
    '''expresion : ID
                | CINT'''
    linea = obtener_linea_actual(p)
    
    if isinstance(p[1], int):
        agregar_simbolo(str(p[1]), 'CINT', 'Constante entera')
        p[0] = NodoOperacion('termino', str(p[1]), None, None, linea)
        p[0].tipo_dato = 'Int'
    else:
        agregar_simbolo(p[1], 'ID', 'Variable en expresión')
        variable = analizador_sem.usar_variable(p[1], linea)
        p[0] = NodoOperacion('ID', p[1], None, None, linea)
        p[0].tipo_dato = variable.tipo if variable else 'Int'

def p_llamada_funcion(p):
    '''llamada_funcion : IMPCAD PAREN parametro TESIS PC
                      | IMPDIG PAREN parametro TESIS PC
                      | LEERDIG PAREN ID TESIS PC'''
    linea = obtener_linea_actual(p)
    
    if p[1] in ('impcad', 'impdig'):
        token = 'IMPCAD' if p[1] == 'impcad' else 'IMPDIG'
        descripcion = 'Función imprimir cadena' if p[1] == 'impcad' else 'Función imprimir dígito'
        agregar_simbolo(p[1], token, descripcion)
    
        param = p[3] if p[3] else "None"
        cuadruplos_globales.append((p[1], param, None, None))

        if p[1] == 'impdig':
            if p[3] is not None:
                if not (isinstance(p[3], str) and p[3].startswith('"') and p[3].endswith('"')):
                    variable = analizador_sem.usar_variable(p[3], linea)
                    if variable and variable.tipo != 'Int':
                        error = ErrorSemantico(
                            linea=linea,
                            tipo="PARAMETRO_TIPO_INCORRECTO",
                            descripcion=f"La función 'impdig' requiere parámetro de tipo 'Int'",
                            contexto=f"Se pasó variable '{p[3]}' de tipo '{variable.tipo}' a función 'impdig'",
                            sugerencia="Use una variable de tipo 'Int' o un número entero"
                        )
                        errores_semanticos.append(error)
        
        elif p[1] == 'impcad':
            if p[3] is not None:
                if not (isinstance(p[3], str) and p[3].startswith('"') and p[3].endswith('"')):
                    variable = analizador_sem.usar_variable(p[3], linea)
                    if variable and variable.tipo != 'Cad':
                        error = ErrorSemantico(
                            linea=linea,
                            tipo="PARAMETRO_TIPO_INCORRECTO",
                            descripcion=f"La función 'impcad' requiere parámetro de tipo 'Cad'",
                            contexto=f"Se pasó variable '{p[3]}' de tipo '{variable.tipo}' a función 'impcad'",
                            sugerencia="Use una variable de tipo 'Cad' o una cadena literal"
                        )
                        errores_semanticos.append(error)
            
    elif p[1] == 'leerdig':
        agregar_simbolo('leerdig', 'LEERDIG', 'Función leer dígito')
        cuadruplos_globales.append(('leerdig', None, None, p[3]))
        
        if p[3] is not None:
            agregar_simbolo(p[3], 'ID', 'Variable para leer')
            variable = analizador_sem.usar_variable(p[3], linea)
            if variable and variable.tipo != 'Int':
                error = ErrorSemantico(
                    linea=linea,
                    tipo="PARAMETRO_TIPO_INCORRECTO",
                    descripcion=f"La función 'leerdig' requiere variable de tipo 'Int'",
                    contexto=f"Se pasó variable '{p[3]}' de tipo '{variable.tipo}' a función 'leerdig'",
                    sugerencia="Use una variable de tipo 'Int'"
                )
                errores_semanticos.append(error)
            else:
                if variable:
                    variable.inicializada = True
    
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')

def p_parametro(p):
    '''parametro : CAD
                | ID'''
    if p[1].startswith('"') and p[1].endswith('"'):
        agregar_simbolo(p[1], 'CAD', 'Literal de cadena')
        p[0] = p[1]
    else:
        agregar_simbolo(p[1], 'ID', 'Variable como parámetro')
        p[0] = p[1]

def p_error(p):
    """Maneja errores sintácticos"""
    try:
        if p:
            token_descripcion = obtener_descripcion_token(p.type, p.value)
            linea = getattr(p, 'lineno', 'desconocida')
            errores.append({
                'line': linea,
                'value': str(p.value) if p.value is not None else 'None',
                'type': 'ERROR_SINTACTICO',
                'desc': f"Error de sintaxis: se encontró {token_descripcion}"
            })
        else:
            errores.append({
                'line': 'EOF',
                'value': 'EOF',
                'type': 'ERROR_SINTACTICO',
                'desc': "Error de sintaxis: fin de archivo inesperado"
            })
    except Exception as e:
        errores.append({
            'line': 'desconocida',
            'value': 'error_interno',
            'type': 'ERROR_SINTACTICO',
            'desc': "Error de sintaxis: error interno del parser"
        })

def obtener_descripcion_token(tipo_token, valor_token):
    """Obtiene una descripción legible del token para mensajes de error"""
    descripciones = {
        'TESIS': 'paréntesis de cierre ")"',
        'PAREN': 'paréntesis de apertura "("',
        'PC': 'punto y coma ";"',
        'ID': f'identificador "{valor_token}"',
        'CINT': f'número "{valor_token}"',
    }
    return descripciones.get(tipo_token, f'token {tipo_token}')

parser = yacc.yacc()

# ================= FUNCIONES PARA EVALUACIÓN Y GENERACIÓN DE CÓDIGO =================

def expresion_a_texto(nodo, precedencia_padre=0):
    """Convierte un árbol de expresión a texto legible"""
    if nodo is None:
        return ""
    precedencias = {'+': 1, '-': 1, '*': 2, '/': 2}
    if nodo.tipo == 'operacion':
        precedencia_actual = precedencias.get(nodo.valor, 0)
        if nodo.izquierdo is None:
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{nodo.valor}{der_texto}"
        else:
            izq_texto = expresion_a_texto(nodo.izquierdo, precedencia_actual)
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{izq_texto} {nodo.valor} {der_texto}"
        if precedencia_actual < precedencia_padre:
            expresion = f"({expresion})"
        return expresion
    elif nodo.tipo in ('termino', 'ID'):
        return str(nodo.valor)
    return str(nodo.valor)

def imprimir_arbol_operacion(nodo, nivel=0):
    """Imprime el árbol de operaciones de forma jerárquica"""
    if nodo is None:
        return ""
    indentacion = "  " * nivel
    resultado = ""
    if nodo.tipo == 'operacion':
        resultado += f"{indentacion}operacion: {nodo.valor}\n"
        if nodo.izquierdo:
            resultado += imprimir_arbol_operacion(nodo.izquierdo, nivel + 1)
        if nodo.derecho:
            resultado += imprimir_arbol_operacion(nodo.derecho, nivel + 1)
    elif nodo.tipo == 'termino':
        resultado += f"{indentacion}termino: {nodo.valor}\n"
    elif nodo.tipo == 'ID':
        resultado += f"{indentacion}ID: {nodo.valor}\n"
    return resultado

def evaluar_nodo(nodo):
    """Evalúa un nodo del árbol y retorna su valor y tipo"""
    if nodo is None:
        return None, None
    if nodo.tipo == 'termino':
        try:
            v = int(nodo.valor)
            return v, 'Int'
        except Exception:
            return None, None
    if nodo.tipo == 'ID':
        nombre = nodo.valor
        var = analizador_sem.variables.get(nombre)
        if var is None or not var.inicializada:
            return None, None
        return var.valor, var.tipo
    if nodo.tipo == 'operacion':
        op = nodo.valor
        if nodo.izquierdo is None:
            rv, rt = evaluar_nodo(nodo.derecho)
            if rv is None or rt != 'Int':
                return None, None
            if op == '-':
                return -rv, 'Int'
            return None, None
        lv, lt = evaluar_nodo(nodo.izquierdo)
        rv, rt = evaluar_nodo(nodo.derecho)
        if lv is None or rv is None or lt != 'Int' or rt != 'Int':
            return None, None
        try:
            if op == '+':
                return lv + rv, 'Int'
            elif op == '-':
                return lv - rv, 'Int'
            elif op == '*':
                return lv * rv, 'Int'
            elif op == '/':
                if rv == 0:
                    return None, None
                return lv // rv, 'Int'
        except Exception:
            return None, None
    return None, None

def generar_cuadruplos_desde_nodo(nodo, quads=None):
    """Genera cuádruplos (código intermedio) desde un nodo del árbol"""
    if quads is None:
        quads = []
    if nodo is None:
        return None, quads
    if nodo.tipo == 'termino':
        return nodo.valor, quads
    if nodo.tipo == 'ID':
        return nodo.valor, quads
    if nodo.tipo == 'operacion' and nodo.izquierdo is None:
        op = nodo.valor
        operando_d, quads = generar_cuadruplos_desde_nodo(nodo.derecho, quads)
        t = nuevo_temp()
        quads.append((op, operando_d, None, t))
        return t, quads
    if nodo.tipo == 'operacion':
        op = nodo.valor
        left_operand, quads = generar_cuadruplos_desde_nodo(nodo.izquierdo, quads)
        right_operand, quads = generar_cuadruplos_desde_nodo(nodo.derecho, quads)
        t = nuevo_temp()
        quads.append((op, left_operand, right_operand, t))
        return t, quads
    return None, quads

def generar_codigo_intermedio_formateado():
    """Genera código intermedio en formato de tres direcciones legible"""
    global codigo_intermedio
    codigo_intermedio = []
    
    if not cuadruplos_globales:
        return "No se generó código intermedio.\n"
    
    resultado =  "╔═══════════════════════════════════════════════════════════╗\n"
    resultado += "║          CÓDIGO INTERMEDIO DE TRES DIRECCIONES           ║\n"
    resultado += "╚═══════════════════════════════════════════════════════════╝\n\n"
    
    for i, cuad in enumerate(cuadruplos_globales, 1):
        op, arg1, arg2, res = cuad
        linea_num = f"{i:03d}"
        
        # Formatear según el tipo de operación
        if op == ':=':
            linea_codigo = f"{linea_num}: {res} = {arg1}"
        elif op in ['+', '-', '*', '/']:
            if arg2 is None:  # Operación unaria
                linea_codigo = f"{linea_num}: {res} = {op}{arg1}"
            else:  # Operación binaria
                linea_codigo = f"{linea_num}: {res} = {arg1} {op} {arg2}"
        elif op == 'impcad':
            linea_codigo = f"{linea_num}: print({arg1})"
        elif op == 'impdig':
            linea_codigo = f"{linea_num}: print({arg1})"
        elif op == 'leerdig':
            linea_codigo = f"{linea_num}: read({res})"
        elif op == 'label':
            linea_codigo = f"{linea_num}: {res}:"
        elif op == 'goto':
            linea_codigo = f"{linea_num}: goto {res}"
        elif op == 'if_false':
            linea_codigo = f"{linea_num}: if_false {arg1} goto {res}"
        else:
            linea_codigo = f"{linea_num}: {op} {arg1} {arg2} {res}"
        
        codigo_intermedio.append(linea_codigo)
        resultado += linea_codigo + "\n"
    
    resultado += "\n" + "─" * 60 + "\n"
    resultado += f"Total de instrucciones: {len(cuadruplos_globales)}\n"
    
    return resultado

def generar_reporte_semantico():
    """Genera un reporte completo del análisis semántico"""
    if not errores_semanticos and not analizador_sem.variables:
        return "No se realizó análisis semántico."
    resultado = "╔═══════════════════════════════════════════════════════════╗\n"
    resultado += "║              REPORTE DE ANÁLISIS SEMÁNTICO                ║\n"
    resultado += "╚═══════════════════════════════════════════════════════════╝\n\n"
    
    resultado += "┌─ TABLA DE VARIABLES DECLARADAS ─────────────────────────┐\n"
    if analizador_sem.variables:
        resultado += f"│ {'Variable':<15} {'Tipo':<8} {'Línea':<6} {'Inic.':<6} {'Usada':<6} │\n"
        resultado += "├" + "─"*58 + "┤\n"
        for nombre, var in analizador_sem.variables.items():
            inicializada = "Sí" if var.inicializada else "No"
            usada = "Sí" if var.usada else "No"
            resultado += f"│ {nombre:<15} {var.tipo:<8} {var.linea_declaracion:<6} {inicializada:<6} {usada:<6} │\n"
    else:
        resultado += "│ No se encontraron variables declaradas.                  │\n"
    resultado += "└" + "─"*58 + "┘\n\n"
    
    resultado += "┌─ ESTADÍSTICAS ──────────────────────────────────────────┐\n"
    resultado += f"│ Variables declaradas: {len(analizador_sem.variables):<35} │\n"
    resultado += f"│ Variables utilizadas: {len(analizador_sem.variables_utilizadas):<35} │\n"
    resultado += f"│ Errores semánticos:   {len(errores_semanticos):<35} │\n"
    resultado += "└" + "─"*58 + "┘\n\n"
    
    if errores_semanticos:
        resultado += "┌─ ERRORES SEMÁNTICOS ────────────────────────────────────┐\n"
        for i, error in enumerate(errores_semanticos, 1):
            resultado += f"│ Error #{i}:\n"
            resultado += f"│   Línea: {error.linea}\n"
            resultado += f"│   Tipo: {error.tipo}\n"
            resultado += f"│   Descripción: {error.descripcion}\n"
            if error.sugerencia:
                resultado += f"│   Sugerencia: {error.sugerencia}\n"
            resultado += "│\n"
        resultado += "└" + "─"*58 + "┘\n"
    else:
        resultado += "✓ No se encontraron errores semánticos.\n\n"
    
    return resultado

def generar_codigo_ensamblador():
    """Genera código ensamblador x86 desde los cuádruplos"""
    if not cuadruplos_globales:
        return "No se generaron cuádruplos.\n"
    
    resultado = "╔═══════════════════════════════════════════════════════════╗\n"
    resultado += "║          CÓDIGO ENSAMBLADOR EQUIVALENTE (x86)            ║\n"
    resultado += "╚═══════════════════════════════════════════════════════════╝\n\n"
    
    # Sección de datos
    resultado += "section .data\n"
    for nombre, var in analizador_sem.variables.items():
        if var.tipo == 'Int':
            resultado += f"    {nombre} dd 0\n"
        elif var.tipo == 'Cad':
            resultado += f"    {nombre} db 256 dup(0)\n"
    
    # Variables temporales
    for i in range(1, temp_counter + 1):
        resultado += f"    t{i} dd 0\n"
    
    resultado += "\nsection .text\n"
    resultado += "    global _start\n\n"
    resultado += "_start:\n"
    
    for i, cuad in enumerate(cuadruplos_globales, 1):
        op, arg1, arg2, res = cuad
        resultado += f"\n    ; ─── Cuádruplo {i}: {op} {arg1} {arg2} {res} ───\n"
        
        if op == ':=':
            resultado += f"    MOV EAX, [{arg1}]\n"
            resultado += f"    MOV [{res}], EAX\n"
        elif op == '+':
            resultado += f"    MOV EAX, [{arg1}]\n"
            resultado += f"    ADD EAX, [{arg2}]\n"
            resultado += f"    MOV [{res}], EAX\n"
        elif op == '-':
            if arg2 is None:
                resultado += f"    MOV EAX, [{arg1}]\n"
                resultado += f"    NEG EAX\n"
                resultado += f"    MOV [{res}], EAX\n"
            else:
                resultado += f"    MOV EAX, [{arg1}]\n"
                resultado += f"    SUB EAX, [{arg2}]\n"
                resultado += f"    MOV [{res}], EAX\n"
        elif op == '*':
            resultado += f"    MOV EAX, [{arg1}]\n"
            resultado += f"    IMUL EAX, [{arg2}]\n"
            resultado += f"    MOV [{res}], EAX\n"
        elif op == '/':
            resultado += f"    MOV EAX, [{arg1}]\n"
            resultado += f"    CDQ\n"
            resultado += f"    IDIV DWORD [{arg2}]\n"
            resultado += f"    MOV [{res}], EAX\n"
        elif op == 'impcad':
            resultado += f"    ; Imprimir cadena {arg1}\n"
            resultado += f"    PUSH {arg1}\n"
            resultado += f"    CALL print_string\n"
        elif op == 'impdig':
            resultado += f"    ; Imprimir entero {arg1}\n"
            resultado += f"    PUSH DWORD [{arg1}]\n"
            resultado += f"    CALL print_int\n"
        elif op == 'leerdig':
            resultado += f"    ; Leer entero en {res}\n"
            resultado += f"    CALL read_int\n"
            resultado += f"    MOV [{res}], EAX\n"
        elif op == 'label':
            resultado += f"{res}:\n"
        elif op == 'goto':
            resultado += f"    JMP {res}\n"
        elif op == 'if_false':
            resultado += f"    CMP DWORD [{arg1}], 0\n"
            resultado += f"    JE {res}\n"
    
    resultado += "\n    ; Salir del programa\n"
    resultado += "    MOV EAX, 1\n"
    resultado += "    XOR EBX, EBX\n"
    resultado += "    INT 0x80\n"
    
    return resultado

def generar_codigo_fuente():
    """Genera el reporte completo de cuádruplos y código ensamblador"""
    if not cuadruplos_globales:
        return "No se generaron cuádruplos.\n"
    
    resultado = "╔═══════════════════════════════════════════════════════════╗\n"
    resultado += "║                  CUÁDRUPLOS GENERADOS                     ║\n"
    resultado += "╚═══════════════════════════════════════════════════════════╝\n\n"
    
    resultado += f"{'#':<5} {'Operador':<12} {'Arg1':<12} {'Arg2':<12} {'Resultado':<12}\n"
    resultado += "─" * 60 + "\n"
    for i, cuad in enumerate(cuadruplos_globales, 1):
        op, arg1, arg2, res = cuad
        arg1_str = str(arg1) if arg1 is not None else '─'
        arg2_str = str(arg2) if arg2 is not None else '─'
        res_str = str(res) if res is not None else '─'
        resultado += f"{i:<5} {op:<12} {arg1_str:<12} {arg2_str:<12} {res_str:<12}\n"
    
    resultado += "\n" + "═" * 60 + "\n\n"
    resultado += generar_codigo_ensamblador()
    
    return resultado

# ================= INTERFAZ GRÁFICA =================
class AnalizadorGUI:
    """Interfaz gráfica del compilador"""
    def __init__(self, root):
        self.root = root
        self.root.title("Compilador PF2024 - Automatas 2")
        self.root.geometry("1400x900")
        
        style = ttk.Style()
        style.theme_use('clam')
        
        self.color_bg = "#f0f0f0"
        self.color_primary = "#2c3e50"
        self.color_success = "#27ae60"
        self.color_error = "#e74c3c"
        self.color_warning = "#f39c12"
        
        self.root.configure(bg=self.color_bg)
        
        self.crear_barra_superior()
        self.crear_area_trabajo()
        
    def crear_barra_superior(self):
        """Crea la barra superior con título y botones principales"""
        barra = tk.Frame(self.root, bg=self.color_primary, height=80)
        barra.pack(fill='x', side='top')
        
        # Título
        titulo = tk.Label(barra, text="COMPILADOR PF2024", 
                         font=('Arial', 20, 'bold'), 
                         bg=self.color_primary, fg='white')
        titulo.pack(side='left', padx=20, pady=15)
        
        subtitulo = tk.Label(barra, text="Análisis Léxico • Sintáctico • Semántico • Generación de Código", 
                            font=('Arial', 10), 
                            bg=self.color_primary, fg='#ecf0f1')
        subtitulo.pack(side='left', padx=5)
        
        # Botones principales
        btn_frame = tk.Frame(barra, bg=self.color_primary)
        btn_frame.pack(side='right', padx=20)
        
        btn_analizar = tk.Button(btn_frame, text="Analizar", 
                                command=self.analizar,
                                bg=self.color_success, fg='white',
                                font=('Arial', 11, 'bold'),
                                padx=20, pady=8, relief='flat',
                                cursor='hand2')
        btn_analizar.pack(side='left', padx=5)
        
        btn_limpiar = tk.Button(btn_frame, text="Limpiar", 
                               command=self.limpiar_todo,
                               bg=self.color_warning, fg='white',
                               font=('Arial', 11, 'bold'),
                               padx=20, pady=8, relief='flat',
                               cursor='hand2')
        btn_limpiar.pack(side='left', padx=5)
        
        btn_cargar = tk.Button(btn_frame, text="Cargar", 
                              command=self.cargar_archivo,
                              bg='#3498db', fg='white',
                              font=('Arial', 11, 'bold'),
                              padx=20, pady=8, relief='flat',
                              cursor='hand2')
        btn_cargar.pack(side='left', padx=5)
    
    def crear_area_trabajo(self):
        """Crea el área de trabajo con pestañas"""
        # Frame contenedor
        container = tk.Frame(self.root, bg=self.color_bg)
        container.pack(fill='both', expand=True, padx=10, pady=10)
        
        # Panel izquierdo - Editor de código
        panel_izq = tk.Frame(container, bg='white', relief='solid', borderwidth=1)
        panel_izq.pack(side='left', fill='both', expand=True, padx=(0, 5))
        
        # Título del editor
        titulo_editor = tk.Label(panel_izq, text="Editor de Código Fuente", 
                                font=('Arial', 12, 'bold'),
                                bg='white', fg=self.color_primary)
        titulo_editor.pack(pady=10)
        
        # Editor de código
        editor_frame = tk.Frame(panel_izq, bg='white')
        editor_frame.pack(fill='both', expand=True, padx=10, pady=(0, 10))
        
        self.codigo_text = scrolledtext.ScrolledText(editor_frame, 
                                                     height=25, 
                                                     font=('Consolas', 11),
                                                     wrap=tk.NONE,
                                                     bg='#fafafa',
                                                     fg='#2c3e50',
                                                     insertbackground='#e74c3c',
                                                     selectbackground='#3498db',
                                                     selectforeground='white')
        self.codigo_text.pack(fill='both', expand=True)
        
        # Código de ejemplo
        codigo_ejemplo = '''pf2024 programa
decl
Int a, b, resultado;
Cad mensaje;

Inicio
a := 5;
b := 3;
resultado := a + b * 2;
mensaje := "Hola Mundo";
impcad(mensaje);
leerdig(a);
Fin'''
        self.codigo_text.insert('1.0', codigo_ejemplo)
        
        # Panel derecho - Resultados con pestañas
        panel_der = tk.Frame(container, bg='white', relief='solid', borderwidth=1)
        panel_der.pack(side='right', fill='both', expand=True, padx=(5, 0))
        
        # Notebook para pestañas
        self.notebook = ttk.Notebook(panel_der)
        self.notebook.pack(fill='both', expand=True, padx=5, pady=5)
        
        # Crear pestañas
        self.crear_pestana_simbolos()
        self.crear_pestana_codigo_intermedio()
        self.crear_pestana_semantico()
        self.crear_pestana_cuadruplos()
        self.crear_pestana_errores()
        
    def crear_pestana_simbolos(self):
        """Pestaña de tabla de símbolos"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="Tabla de Símbolos")
        
        # Treeview para la tabla
        columns = ('No.', 'Lexema', 'Token', 'Referencia')
        self.tabla_tree = ttk.Treeview(frame, columns=columns, show='headings', height=20)
        
        for col in columns:
            self.tabla_tree.heading(col, text=col)
            self.tabla_tree.column(col, width=120)
        
        self.tabla_tree.pack(fill='both', expand=True, padx=10, pady=10)
        
        scrollbar = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=self.tabla_tree.yview)
        scrollbar.pack(side='right', fill='y')
        self.tabla_tree.configure(yscrollcommand=scrollbar.set)
    
    def crear_pestana_codigo_intermedio(self):
        """Pestaña de código intermedio"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="Código Intermedio")
        
        self.intermedio_text = scrolledtext.ScrolledText(frame, 
                                                         height=30, 
                                                         font=('Consolas', 10),
                                                         bg='#fafafa',
                                                         fg='#2c3e50')
        self.intermedio_text.pack(fill='both', expand=True, padx=10, pady=10)
    
    def crear_pestana_semantico(self):
        """Pestaña de análisis semántico"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="Análisis Semántico")
        
        self.semantico_text = scrolledtext.ScrolledText(frame, 
                                                        height=30, 
                                                        font=('Consolas', 10),
                                                        bg='#fafafa',
                                                        fg='#2c3e50')
        self.semantico_text.pack(fill='both', expand=True, padx=10, pady=10)
    
    def crear_pestana_cuadruplos(self):
        """Pestaña de cuádruplos y ensamblador"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="Cuádruplos & ASM")
        
        self.cuadruplos_text = scrolledtext.ScrolledText(frame, 
                                                         height=30, 
                                                         font=('Consolas', 10),
                                                         bg='#fafafa',
                                                         fg='#2c3e50')
        self.cuadruplos_text.pack(fill='both', expand=True, padx=10, pady=10)
    
    def crear_pestana_errores(self):
        """Pestaña de errores"""
        frame = ttk.Frame(self.notebook)
        self.notebook.add(frame, text="Errores")
        
        self.errores_text = scrolledtext.ScrolledText(frame, 
                                                      height=30, 
                                                      font=('Consolas', 10),
                                                      bg='#fff5f5',
                                                      fg='#c0392b')
        self.errores_text.pack(fill='both', expand=True, padx=10, pady=10)

    def analizar(self):
        """Ejecuta el análisis completo del código"""
        reiniciar_datos()
        
        # Limpiar todas las áreas de texto
        self.errores_text.delete('1.0', tk.END)
        self.intermedio_text.delete('1.0', tk.END)
        self.semantico_text.delete('1.0', tk.END)
        self.cuadruplos_text.delete('1.0', tk.END)
        
        codigo = self.codigo_text.get('1.0', tk.END)
        global lineas_codigo
        lineas_codigo = codigo.split('\n')
        
        try:
            # Análisis léxico y sintáctico
            self.reiniciar_lexer()
            analizador_lexico.input(codigo)
            self.reiniciar_lexer()
            analizador_lexico.input(codigo)
            parser.parse(lexer=analizador_lexico)
            
            # Actualizar resultados
            self.actualizar_tabla()
            self.intermedio_text.insert('1.0', generar_codigo_intermedio_formateado())
            self.semantico_text.insert('1.0', generar_reporte_semantico())
            self.cuadruplos_text.insert('1.0', generar_codigo_fuente())
            
            # Mostrar errores
            if errores or errores_semanticos:
                self.errores_text.insert(tk.END, "╔═══════════════════════════════════════════════════════════╗\n")
                self.errores_text.insert(tk.END, "║                  ERRORES ENCONTRADOS                      ║\n")
                self.errores_text.insert(tk.END, "╚═══════════════════════════════════════════════════════════╝\n\n")
                
                if errores:
                    self.errores_text.insert(tk.END, "┌─ ERRORES LÉXICOS Y SINTÁCTICOS ─────────────────────────┐\n")
                    for i, error in enumerate(errores, 1):
                        self.errores_text.insert(tk.END, f"│ Error #{i}: Línea {error['line']}\n")
                        self.errores_text.insert(tk.END, f"│   {error['desc']}\n")
                        self.errores_text.insert(tk.END, "│\n")
                    self.errores_text.insert(tk.END, "└" + "─"*58 + "┘\n\n")
                
                if errores_semanticos:
                    self.errores_text.insert(tk.END, "┌─ ERRORES SEMÁNTICOS ────────────────────────────────────┐\n")
                    for i, error in enumerate(errores_semanticos, 1):
                        self.errores_text.insert(tk.END, f"│ Error #{i}: Línea {error.linea}\n")
                        self.errores_text.insert(tk.END, f"│   Tipo: {error.tipo}\n")
                        self.errores_text.insert(tk.END, f"│   {error.descripcion}\n")
                        if error.sugerencia:
                            self.errores_text.insert(tk.END, f"│   {error.sugerencia}\n")
                        self.errores_text.insert(tk.END, "│\n")
                    self.errores_text.insert(tk.END, "└" + "─"*58 + "┘\n")
                
                messagebox.showwarning("Análisis Completado", 
                                      f"Se encontraron {len(errores) + len(errores_semanticos)} errores.\nRevise la pestaña de Errores.")
            else:
                self.errores_text.insert(tk.END, "¡Análisis completado exitosamente!\n\n")
                self.errores_text.insert(tk.END, "No se encontraron errores léxicos, sintácticos ni semánticos.\n")
                messagebox.showinfo("Éxito", "¡Análisis completado sin errores!")
                
        except Exception as e:
            self.errores_text.insert(tk.END, f"Error crítico: {str(e)}\n")
            messagebox.showerror("Error", f"Error durante el análisis:\n{str(e)}")
    
    def actualizar_tabla(self):
        """Actualiza la tabla de símbolos"""
        for item in self.tabla_tree.get_children():
            self.tabla_tree.delete(item)
        for simbolo in tabla_simbolos:
            self.tabla_tree.insert('', 'end', values=(
                simbolo.numero, simbolo.lexema, simbolo.token, simbolo.referencia or ''
            ))
    
    def limpiar_todo(self):
        """Limpia todos los resultados"""
        reiniciar_datos()
        self.actualizar_tabla()
        self.errores_text.delete('1.0', tk.END)
        self.intermedio_text.delete('1.0', tk.END)
        self.semantico_text.delete('1.0', tk.END)
        self.cuadruplos_text.delete('1.0', tk.END)
        messagebox.showinfo("Limpieza", "Todos los resultados han sido limpiados.")
    
    def cargar_archivo(self):
        """Carga un archivo de código"""
        file_path = filedialog.askopenfilename(
            title="Seleccionar archivo",
            filetypes=[("Archivos PF2024", "*.pf"), ("Archivos de texto", "*.txt"), ("Todos", "*.*")]
        )
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as file:
                    self.codigo_text.delete('1.0', tk.END)
                    self.codigo_text.insert('1.0', file.read())
                messagebox.showinfo("Éxito", f"Archivo cargado: {file_path}")
            except Exception as e:
                messagebox.showerror("Error", f"Error al cargar el archivo:\n{str(e)}")

    def reiniciar_lexer(self):
        """Reinicia el analizador léxico"""
        analizador_lexico.lineno = 1
        analizador_lexico.lexpos = 0

# ================= PUNTO DE ENTRADA =================
if __name__ == "__main__":
    print("="*70)
    print("COMPILADOR PF2024 - AUTOMATAS 2")
    print("Análisis Léxico, Sintáctico, Semántico y Generación de Código")
    print("="*70)
    root = tk.Tk()
    app = AnalizadorGUI(root)
    root.mainloop()
