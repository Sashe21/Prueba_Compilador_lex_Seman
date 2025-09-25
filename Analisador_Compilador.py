"""
Commit de toño
ANALIZADOR SEMÁNTICO PF2024 - VERSIÓN COMPLETA
Incluye análisis semántico con detección de errores detallada
"""

import ply.lex as lex
import ply.yacc as yacc
import tkinter as tk
from tkinter import scrolledtext, ttk, filedialog
import re

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
lineas_codigo = []  # Para mostrar contexto de errores
tabla_tipos = {}  # Para almacenar tipos de variables

# ================= CLASES PARA ANÁLISIS SEMÁNTICO =================

class ErrorSemantico:
    def __init__(self, linea, tipo, descripcion, contexto, sugerencia=None):
        self.linea = linea
        self.tipo = tipo
        self.descripcion = descripcion
        self.contexto = contexto
        self.sugerencia = sugerencia

class Variable:
    def __init__(self, nombre, tipo, linea_declaracion, inicializada=False):
        self.nombre = nombre
        self.tipo = tipo
        self.linea_declaracion = linea_declaracion
        self.inicializada = inicializada
        self.usada = False
        self.lineas_uso = []

class AnalizadorSemantico:
    def __init__(self):
        self.variables = {}  # nombre -> Variable
        self.variables_declaradas = set()
        self.variables_utilizadas = set()
        self.en_declaracion = False
        self.tipo_actual = None
        self.linea_actual = 1
        
    def reiniciar(self):
        self.variables = {}
        self.variables_declaradas = set()
        self.variables_utilizadas = set()
        self.en_declaracion = False
        self.tipo_actual = None
        self.linea_actual = 1

    def declarar_variable(self, nombre, tipo, linea):
        """Declara una variable y verifica duplicados"""
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
        """Verifica compatibilidad de tipos en asignación"""
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
        """Verifica que los operandos sean compatibles con operaciones aritméticas"""
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
        """Identifica variables declaradas pero no utilizadas"""
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
        """Identifica variables utilizadas sin inicializar"""
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

# Instancia global del analizador semántico
analizador_sem = AnalizadorSemantico()

# ================= CLASES AUXILIARES =================
class NodoOperacion:
    def __init__(self, tipo, valor=None, izquierdo=None, derecho=None, linea=None):
        self.tipo = tipo
        self.valor = valor
        self.izquierdo = izquierdo
        self.derecho = derecho
        self.linea = linea or 1
        self.tipo_dato = None  # Para análisis semántico
    
    def __str__(self):
        if self.tipo == 'operacion':
            return f"operacion: {self.valor}"
        elif self.tipo == 'termino':
            return f"termino: {self.valor}"
        elif self.tipo == 'ID':
            return f"ID: {self.valor}"
        else:
            return str(self.valor)

class SimboloTabla:
    def __init__(self, lexema, token, referencia=None):
        global contador_simbolos
        self.numero = contador_simbolos
        self.lexema = lexema
        self.token = token
        self.referencia = referencia
        contador_simbolos += 1

# ================= FUNCIONES AUXILIARES =================
def agregar_simbolo(lexema, token, referencia=None):
    for simbolo in tabla_simbolos:
        if simbolo.lexema == lexema and simbolo.token == token:
            return simbolo
    nuevo_simbolo = SimboloTabla(lexema, token, referencia)
    tabla_simbolos.append(nuevo_simbolo)
    return nuevo_simbolo

def reiniciar_datos():
    global errores, errores_semanticos, tabla_simbolos, contador_simbolos, arboles_operaciones, lineas_codigo, tabla_tipos
    errores = []
    errores_semanticos = []
    tabla_simbolos = []
    contador_simbolos = 1
    arboles_operaciones = []
    lineas_codigo = []
    tabla_tipos = {}
    analizador_sem.reiniciar()

def obtener_linea_actual(p):
    """Obtiene el número de línea del token actual de forma segura"""
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

def validar_parametro(parametro, nombre_funcion, tipo_esperado, linea):
    """Valida un parámetro de función de forma segura"""
    if parametro is None:
        error = ErrorSemantico(
            linea=linea,
            tipo="PARAMETRO_FALTANTE",
            descripcion=f"La función '{nombre_funcion}' requiere un parámetro",
            contexto=f"Llamada a '{nombre_funcion}' sin parámetro",
            sugerencia=f"Proporcione un parámetro de tipo '{tipo_esperado}'"
        )
        errores_semanticos.append(error)
        return False
    
    if not isinstance(parametro, str):
        error = ErrorSemantico(
            linea=linea,
            tipo="PARAMETRO_INVALIDO",
            descripcion=f"Parámetro inválido para función '{nombre_funcion}'",
            contexto=f"Se esperaba un parámetro válido",
            sugerencia=f"Verifique la sintaxis de la llamada a '{nombre_funcion}'"
        )
        errores_semanticos.append(error)
        return False
    
    return True

# ================= FUNCIONES DE TOKENS =================

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
    errores.append({
        'line': t.lineno,
        'value': t.value[0],
        'type': 'ERROR_LEXICO',
        'desc': f'Carácter ilegal "{t.value[0]}"'
    })
    t.lexer.skip(1)

# Construcción del analizador léxico
analizador_lexico = lex.lex()

# ================= ANALIZADOR SINTÁCTICO CON ANÁLIIS SEMÁNTICO =================

precedence = (
    ('left', 'MAS', 'MENOS'),
    ('left', 'MUL', 'DIV'),
    ('right', 'UMINUS'),
)

# ================= REGLAS GRAMATICALES CON ANÁLISIS SEMÁNTICO =================

def p_programa(p):
    '''programa : PROG ID programa_decl'''
    agregar_simbolo(p[1], 'PROG', 'Palabra clave del programa')
    agregar_simbolo(p[2], 'ID', 'Nombre del programa')
    
    # Verificaciones semánticas finales
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
        # Análisis semántico: declarar variable
        analizador_sem.declarar_variable(p[1], analizador_sem.tipo_actual, linea)
    else:
        agregar_simbolo(p[1], 'ID', 'Variable')
        agregar_simbolo(',', 'COMA', 'Separador de variables')
        # Análisis semántico: declarar variable
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
                  | llamada_funcion'''
    pass

def p_asignacion(p):
    '''asignacion : ID ASIG expresion PC'''
    linea = obtener_linea_actual(p)
    
    agregar_simbolo(p[1], 'ID', 'Variable en asignación')
    agregar_simbolo(':=', 'ASIG', 'Operador de asignación')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')
    
    # Análisis semántico: verificar asignación
    tipo_expresion = None
    if p[3]:
        tipo_expresion = getattr(p[3], 'tipo_dato', 'Int')  # Asumir Int por defecto
    
    analizador_sem.asignar_variable(p[1], tipo_expresion, linea)
    
    # Guardar la operación aritmética
    if p[3] and hasattr(p[3], 'tipo') and p[3].tipo in ['operacion', 'termino', 'ID']:
        arboles_operaciones.append({
            'variable': p[1],
            'expresion': p[3],
            'linea': linea
        })

def p_expresion_binaria(p):
    '''expresion : expresion MAS expresion
                | expresion MENOS expresion
                | expresion MUL expresion
                | expresion DIV expresion'''
    linea = obtener_linea_actual(p)
    
    # Análisis semántico: verificar operandos
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
        
        # Verificación semántica adicional: división por cero
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
        # Análisis semántico: usar variable
        variable = analizador_sem.usar_variable(p[1], linea)
        p[0] = NodoOperacion('ID', p[1], None, None, linea)
        p[0].tipo_dato = variable.tipo if variable else 'Int'

def p_llamada_funcion(p):
    '''llamada_funcion : IMPCAD PAREN parametro TESIS PC
                      | LEERDIG PAREN ID TESIS PC'''
    linea = obtener_linea_actual(p)
    
    if p[1] == 'impcad':
        agregar_simbolo('impcad', 'IMPCAD', 'Función imprimir cadena')
        # Verificar que el parámetro no sea None
        if p[3] is not None:
            # Verificar tipo del parámetro
            if not (isinstance(p[3], str) and p[3].startswith('"') and p[3].endswith('"')):
                # Es una variable, verificar que sea de tipo Cad
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
        else:
            # Error: parámetro faltante
            error = ErrorSemantico(
                linea=linea,
                tipo="PARAMETRO_FALTANTE",
                descripcion="La función 'impcad' requiere un parámetro",
                contexto="Llamada a 'impcad' sin parámetro",
                sugerencia="Proporcione una cadena literal o variable de tipo 'Cad'"
            )
            errores_semanticos.append(error)
            
    elif p[1] == 'leerdig':
        agregar_simbolo('leerdig', 'LEERDIG', 'Función leer dígito')
        # Verificar que el parámetro no sea None
        if p[3] is not None:
            agregar_simbolo(p[3], 'ID', 'Variable para leer')
            # Verificar que la variable sea de tipo Int
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
                # Marcar como inicializada ya que leerdig asigna un valor
                if variable:
                    variable.inicializada = True
        else:
            # Error: parámetro faltante
            error = ErrorSemantico(
                linea=linea,
                tipo="PARAMETRO_FALTANTE",
                descripcion="La función 'leerdig' requiere un parámetro",
                contexto="Llamada a 'leerdig' sin parámetro",
                sugerencia="Proporcione una variable de tipo 'Int'"
            )
            errores_semanticos.append(error)
    
    agregar_simbolo('(', 'PAREN', 'Paréntesis izquierdo')
    agregar_simbolo(')', 'TESIS', 'Paréntesis derecho')
    agregar_simbolo(';', 'PC', 'Fin de instrucción')

def p_parametro(p):
    '''parametro : CAD
                | ID'''
    if p[1].startswith('"') and p[1].endswith('"'):
        agregar_simbolo(p[1], 'CAD', 'Literal de cadena')
        p[0] = p[1]  # Pasar el valor al nivel superior
    else:
        agregar_simbolo(p[1], 'ID', 'Variable como parámetro')
        p[0] = p[1]  # Pasar el valor al nivel superior

def p_error(p):
    """Manejo de errores sintácticos mejorado con más seguridad"""
    try:
        if p:
            token_descripcion = obtener_descripcion_token(p.type, p.value)
            linea = getattr(p, 'lineno', 'desconocida')
            print(f"Error de sintaxis en {token_descripcion} en línea {linea}")
            errores.append({
                'line': linea,
                'value': str(p.value) if p.value is not None else 'None',
                'type': 'ERROR_SINTACTICO',
                'desc': f"Error de sintaxis: se encontró {token_descripcion}"
            })
        else:
            print("Error de sintaxis: fin de archivo inesperado")
            errores.append({
                'line': 'EOF',
                'value': 'EOF',
                'type': 'ERROR_SINTACTICO',
                'desc': "Error de sintaxis: fin de archivo inesperado"
            })
    except Exception as e:
        print(f"Error en el manejo de errores sintácticos: {e}")
        errores.append({
            'line': 'desconocida',
            'value': 'error_interno',
            'type': 'ERROR_SINTACTICO',
            'desc': "Error de sintaxis: error interno del parser"
        })

def obtener_descripcion_token(tipo_token, valor_token):
    """Convierte los tipos de tokens en descripciones más amigables"""
    descripciones = {
        'TESIS': f'paréntesis de cierre ")"',
        'PAREN': f'paréntesis de apertura "("',
        'PC': f'punto y coma ";"',
        'COMA': f'coma ","',
        'MAS': f'operador suma "+"',
        'MENOS': f'operador resta "-"',
        'MUL': f'operador multiplicación "*"',
        'DIV': f'operador división "/"',
        'ASIG': f'operador de asignación ":="',
        'ID': f'identificador "{valor_token}"',
        'CINT': f'número "{valor_token}"',
        'CAD': f'cadena de texto {valor_token}',
        'PROG': f'palabra clave "pf2024"',
        'DECL': f'palabra clave "decl"',
        'INICIO': f'palabra clave "Inicio"',
        'FIN': f'palabra clave "Fin"',
        'TIPO_INT': f'tipo de dato "Int"',
        'TIPO_CAD': f'tipo de dato "Cad"',
        'TIPO_BOOL': f'tipo de dato "Bool"',
        'LEERDIG': f'función "leerdig"',
        'IMPCAD': f'función "impcad"',
    }
    
    if tipo_token in descripciones:
        return descripciones[tipo_token]
    else:
        return f'token {tipo_token} "{valor_token}"'

# Construcción del analizador sintáctico
parser = yacc.yacc()

# ================= FUNCIONES PARA ÁRBOLES =================
def expresion_a_texto(nodo, precedencia_padre=0):
    """Convierte un nodo del árbol a texto"""
    if nodo is None:
        return ""
    
    precedencias = {'+': 1, '-': 1, '*': 2, '/': 2}
    
    if nodo.tipo == 'operacion':
        precedencia_actual = precedencias.get(nodo.valor, 0)
        
        if nodo.izquierdo is None:  # Operador unario
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{nodo.valor}{der_texto}"
        else:  # Operador binario
            izq_texto = expresion_a_texto(nodo.izquierdo, precedencia_actual)
            der_texto = expresion_a_texto(nodo.derecho, precedencia_actual)
            expresion = f"{izq_texto} {nodo.valor} {der_texto}"
        
        if precedencia_actual < precedencia_padre:
            expresion = f"({expresion})"
        
        return expresion
    elif nodo.tipo == 'termino':
        return str(nodo.valor)
    elif nodo.tipo == 'ID':
        return str(nodo.valor)
    else:
        return str(nodo.valor)

def imprimir_arbol_operacion(nodo, nivel=0):
    """Imprime un árbol de operación de forma jerárquica"""
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

def generar_arboles_texto():
    """Genera el texto completo de todos los árboles de operaciones"""
    if not arboles_operaciones:
        return "No se encontraron operaciones aritméticas en el código."
    
    resultado = ""
    for i, operacion in enumerate(arboles_operaciones, 1):
        expresion_texto = expresion_a_texto(operacion['expresion'])
        resultado += f"=== Operación {i}: {operacion['variable']} := {expresion_texto} ===\n"
        resultado += f"Línea: {operacion.get('linea', 'N/A')}\n"
        resultado += f"Árbol sintáctico:\n"
        resultado += imprimir_arbol_operacion(operacion['expresion'])
        resultado += "\n" + "="*60 + "\n\n"
    
    return resultado

def generar_reporte_semantico():
    """Genera un reporte completo del análisis semántico"""
    if not errores_semanticos and not analizador_sem.variables:
        return "No se realizó análisis semántico."
    
    resultado = "REPORTE DE ANÁLISIS SEMÁNTICO\n"
    resultado += "="*50 + "\n\n"
    
    # 1. Tabla de variables
    resultado += "1. TABLA DE VARIABLES DECLARADAS:\n"
    resultado += "-"*40 + "\n"
    if analizador_sem.variables:
        resultado += f"{'Variable':<15} {'Tipo':<8} {'Línea':<6} {'Inicial.':<8} {'Usada':<6} {'Líneas Uso'}\n"
        resultado += "-"*70 + "\n"
        for nombre, var in analizador_sem.variables.items():
            inicializada = "Sí" if var.inicializada else "No"
            usada = "Sí" if var.usada else "No"
            lineas_uso = ", ".join(map(str, var.lineas_uso)) if var.lineas_uso else "-"
            resultado += f"{nombre:<15} {var.tipo:<8} {var.linea_declaracion:<6} {inicializada:<8} {usada:<6} {lineas_uso}\n"
    else:
        resultado += "No se encontraron variables declaradas.\n"
    
    resultado += "\n"
    
    # 2. Estadísticas
    resultado += "2. ESTADÍSTICAS:\n"
    resultado += "-"*20 + "\n"
    resultado += f"Variables declaradas: {len(analizador_sem.variables)}\n"
    resultado += f"Variables utilizadas: {len(analizador_sem.variables_utilizadas)}\n"
    resultado += f"Variables no utilizadas: {len(analizador_sem.variables_declaradas - analizador_sem.variables_utilizadas)}\n"
    resultado += f"Errores semánticos encontrados: {len(errores_semanticos)}\n\n"
    
    # 3. Errores semánticos detallados
    if errores_semanticos:
        resultado += "3. ERRORES SEMÁNTICOS DETALLADOS:\n"
        resultado += "-"*35 + "\n"
        for i, error in enumerate(errores_semanticos, 1):
            resultado += f"Error #{i}:\n"
            resultado += f"  📍 Línea: {error.linea}\n"
            resultado += f"  🏷️  Tipo: {error.tipo}\n"
            resultado += f"  📝 Descripción: {error.descripcion}\n"
            resultado += f"  📄 Contexto: {error.contexto}\n"
            if error.sugerencia:
                resultado += f"  💡 Sugerencia: {error.sugerencia}\n"
            resultado += "\n" + "-"*50 + "\n"
    else:
        resultado += "3. ERRORES SEMÁNTICOS:\n"
        resultado += "-"*20 + "\n"
        resultado += "✅ No se encontraron errores semánticos.\n\n"
    
    return resultado

# ================= INTERFAZ GRÁFICA MEJORADA =================
class AnalizadorGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("Analizador Semántico PF2024 - Completo con Errores Detallados")
        self.root.geometry("1600x1000")
        
        self.notebook = ttk.Notebook(root)
        self.notebook.pack(fill='both', expand=True, padx=10, pady=10)
        
        self.frame_principal = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_principal, text="Análisis Principal")
        
        self.frame_arbol = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_arbol, text="Árboles de Operaciones")
        
        self.frame_semantico = ttk.Frame(self.notebook)
        self.notebook.add(self.frame_semantico, text="Análisis Semántico")
        
        self.crear_interfaz_principal()
        self.crear_interfaz_arbol()
        self.crear_interfaz_semantico()
    
    def crear_interfaz_principal(self):
        main_frame = ttk.Frame(self.frame_principal, padding="10")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        ttk.Label(main_frame, text="Código fuente:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.codigo_text = scrolledtext.ScrolledText(main_frame, height=15, width=80)
        self.codigo_text.grid(row=1, column=0, columnspan=2, sticky=(tk.W, tk.E), pady=(0, 10))
        
        # Código de ejemplo con errores semánticos para demostrar
        codigo_ejemplo = '''pf2024 programa
/* Ejemplo con errores semánticos para demostración */

decl    /* Declaración de variables */

Int a, b, c, resultado, noUsada;
Cad mensaje, otraCad;
Bool flag;
Int a;  // Error: variable duplicada

Inicio    /* Cuerpo del programa */
a := 5;
b := 3;
resultado := a + b * c;  // Error: 'c' no inicializada
d := a + b;  // Error: 'd' no declarada
mensaje := a;  // Error: incompatibilidad de tipos
impcad("Resultado:");
impcad(resultado);  // Error: tipo incorrecto para impcad
leerdig(mensaje);  // Error: tipo incorrecto para leerdig
division := a / 0;  // Error: división por cero
leerdig(nuevaVar);  // Error: variable no declarada
Fin'''
        
        self.codigo_text.insert('1.0', codigo_ejemplo)
        
        button_frame = ttk.Frame(main_frame)
        button_frame.grid(row=2, column=0, columnspan=2, pady=(0, 10))
        
        ttk.Button(button_frame, text="Analizar", command=self.analizar).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(button_frame, text="Limpiar", command=self.limpiar_todo).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(button_frame, text="Cargar Archivo", command=self.cargar_archivo).pack(side=tk.LEFT)
        
        ttk.Label(main_frame, text="Tabla de Símbolos:").grid(row=3, column=0, sticky=tk.W, pady=(10, 5))
        
        columns = ('No.', 'Lexema', 'Token', 'Referencia')
        self.tabla_tree = ttk.Treeview(main_frame, columns=columns, show='headings', height=12)
        
        for col in columns:
            self.tabla_tree.heading(col, text=col)
            self.tabla_tree.column(col, width=150)
        
        self.tabla_tree.grid(row=4, column=0, columnspan=2, sticky=(tk.W, tk.E))
        
        scrollbar = ttk.Scrollbar(main_frame, orient=tk.VERTICAL, command=self.tabla_tree.yview)
        scrollbar.grid(row=4, column=2, sticky=(tk.N, tk.S))
        self.tabla_tree.configure(yscrollcommand=scrollbar.set)
        
        ttk.Label(main_frame, text="Mensajes:").grid(row=5, column=0, sticky=tk.W, pady=(10, 5))
        self.mensajes_text = scrolledtext.ScrolledText(main_frame, height=4, width=80)
        self.mensajes_text.grid(row=6, column=0, columnspan=2, sticky=(tk.W, tk.E))
        
        ttk.Label(main_frame, text="Errores Léxicos y Sintácticos:").grid(row=7, column=0, sticky=tk.W, pady=(10, 5))
        self.errores_text = scrolledtext.ScrolledText(main_frame, height=6, width=80)
        self.errores_text.grid(row=8, column=0, columnspan=2, sticky=(tk.W, tk.E))
        
        self.frame_principal.columnconfigure(0, weight=1)
        self.frame_principal.rowconfigure(0, weight=1)
        main_frame.columnconfigure(0, weight=1)
        main_frame.rowconfigure(1, weight=1)
        main_frame.rowconfigure(4, weight=1)
    
    def crear_interfaz_arbol(self):
        arbol_frame = ttk.Frame(self.frame_arbol, padding="10")
        arbol_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        ttk.Label(arbol_frame, text="Árboles de Operaciones Aritméticas:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        
        self.arbol_text = scrolledtext.ScrolledText(arbol_frame, height=40, width=120, font=('Courier', 10))
        self.arbol_text.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        scrollbar_arbol = ttk.Scrollbar(arbol_frame, orient=tk.VERTICAL, command=self.arbol_text.yview)
        scrollbar_arbol.grid(row=1, column=1, sticky=(tk.N, tk.S))
        self.arbol_text.configure(yscrollcommand=scrollbar_arbol.set)
        
        self.frame_arbol.columnconfigure(0, weight=1)
        self.frame_arbol.rowconfigure(0, weight=1)
        arbol_frame.columnconfigure(0, weight=1)
        arbol_frame.rowconfigure(1, weight=1)
    
    def crear_interfaz_semantico(self):
        sem_frame = ttk.Frame(self.frame_semantico, padding="10")
        sem_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        ttk.Label(sem_frame, text="Reporte de Análisis Semántico:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        
        self.semantico_text = scrolledtext.ScrolledText(sem_frame, height=35, width=120, font=('Courier', 10))
        self.semantico_text.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        scrollbar_sem = ttk.Scrollbar(sem_frame, orient=tk.VERTICAL, command=self.semantico_text.yview)
        scrollbar_sem.grid(row=1, column=1, sticky=(tk.N, tk.S))
        self.semantico_text.configure(yscrollcommand=scrollbar_sem.set)
        
        # Frame para errores semánticos específicos
        ttk.Label(sem_frame, text="Errores Semánticos Detallados:").grid(row=2, column=0, sticky=tk.W, pady=(10, 5))
        
        self.errores_sem_text = scrolledtext.ScrolledText(sem_frame, height=15, width=120, font=('Courier', 9))
        self.errores_sem_text.grid(row=3, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        scrollbar_err_sem = ttk.Scrollbar(sem_frame, orient=tk.VERTICAL, command=self.errores_sem_text.yview)
        scrollbar_err_sem.grid(row=3, column=1, sticky=(tk.N, tk.S))
        self.errores_sem_text.configure(yscrollcommand=scrollbar_err_sem.set)
        
        self.frame_semantico.columnconfigure(0, weight=1)
        self.frame_semantico.rowconfigure(0, weight=1)
        sem_frame.columnconfigure(0, weight=1)
        sem_frame.rowconfigure(1, weight=2)
        sem_frame.rowconfigure(3, weight=1)
    
    def analizar(self):
        global tabla_simbolos, contador_simbolos, errores, errores_semanticos, arboles_operaciones, lineas_codigo
        
        # Reiniciar datos
        reiniciar_datos()
        
        # Limpiar interfaces
        self.mensajes_text.delete('1.0', tk.END)
        self.errores_text.delete('1.0', tk.END)
        self.arbol_text.delete('1.0', tk.END)
        self.semantico_text.delete('1.0', tk.END)
        self.errores_sem_text.delete('1.0', tk.END)
        
        codigo = self.codigo_text.get('1.0', tk.END)
        lineas_codigo = codigo.split('\n')
        
        try:
            # Reiniciar lexer
            self.reiniciar_lexer()
            
            # Análisis léxico
            analizador_lexico.input(codigo)
            
            # Análisis sintáctico y semántico
            self.reiniciar_lexer()
            analizador_lexico.input(codigo)
            resultado = parser.parse(lexer=analizador_lexico)
            
            # Actualizar interfaces
            self.actualizar_tabla()
            
            # Árboles de operaciones
            arboles_texto = generar_arboles_texto()
            self.arbol_text.insert('1.0', arboles_texto)
            
            # Reporte semántico
            reporte_semantico = generar_reporte_semantico()
            self.semantico_text.insert('1.0', reporte_semantico)
            
            # Errores semánticos detallados
            self.mostrar_errores_semanticos_detallados()
            
            # Mensajes de resumen
            total_errores = len(errores) + len(errores_semanticos)
            self.mensajes_text.insert(tk.END, "✅ Análisis completado.\n")
            self.mensajes_text.insert(tk.END, f"📊 Símbolos encontrados: {len(tabla_simbolos)}\n")
            self.mensajes_text.insert(tk.END, f"🧮 Operaciones aritméticas: {len(arboles_operaciones)}\n")
            self.mensajes_text.insert(tk.END, f"🔍 Variables declaradas: {len(analizador_sem.variables)}\n")
            self.mensajes_text.insert(tk.END, f"⚠️  Total de errores: {total_errores}\n")
            self.mensajes_text.insert(tk.END, f"   - Léxicos/Sintácticos: {len(errores)}\n")
            self.mensajes_text.insert(tk.END, f"   - Semánticos: {len(errores_semanticos)}\n")
            
            # Errores léxicos y sintácticos
            if errores:
                self.errores_text.insert(tk.END, "❌ Errores Léxicos y Sintácticos:\n")
                self.errores_text.insert(tk.END, "="*50 + "\n")
                
                for i, error in enumerate(errores, 1):
                    linea_num = error['line']
                    
                    self.errores_text.insert(tk.END, f"Error #{i}:\n")
                    self.errores_text.insert(tk.END, f"  📍 Línea {linea_num}: {error['type']}\n")
                    
                    if 'desc' in error:
                        self.errores_text.insert(tk.END, f"  📝 Descripción: {error['desc']}\n")
                    
                    if isinstance(linea_num, int) and 1 <= linea_num <= len(lineas_codigo):
                        contexto = lineas_codigo[linea_num - 1].strip()
                        if contexto:
                            self.errores_text.insert(tk.END, f"  📄 Código: {contexto}\n")
                    
                    self.errores_text.insert(tk.END, "-"*30 + "\n")
            else:
                self.errores_text.insert(tk.END, "✅ No se encontraron errores léxicos o sintácticos.")

        except Exception as e:
            self.mensajes_text.insert(tk.END, f"❌ Error durante el análisis: {str(e)}\n")
            import traceback
            self.mensajes_text.insert(tk.END, f"Detalles: {traceback.format_exc()}\n")
    
    def mostrar_errores_semanticos_detallados(self):
        """Muestra errores semánticos con formato detallado y coloreado"""
        if not errores_semanticos:
            self.errores_sem_text.insert(tk.END, "✅ No se encontraron errores semánticos.\n")
            return
        
        self.errores_sem_text.insert(tk.END, "❌ ERRORES SEMÁNTICOS DETALLADOS\n")
        self.errores_sem_text.insert(tk.END, "="*70 + "\n\n")
        
        # Agrupar errores por tipo
        errores_por_tipo = {}
        for error in errores_semanticos:
            if error.tipo not in errores_por_tipo:
                errores_por_tipo[error.tipo] = []
            errores_por_tipo[error.tipo].append(error)
        
        # Mostrar resumen por tipo
        self.errores_sem_text.insert(tk.END, "📊 RESUMEN POR TIPO DE ERROR:\n")
        self.errores_sem_text.insert(tk.END, "-"*40 + "\n")
        for tipo, lista_errores in errores_por_tipo.items():
            self.errores_sem_text.insert(tk.END, f"• {tipo}: {len(lista_errores)} error(es)\n")
        self.errores_sem_text.insert(tk.END, "\n")
        
        # Mostrar errores detallados
        for i, error in enumerate(errores_semanticos, 1):
            self.errores_sem_text.insert(tk.END, f"🚨 ERROR SEMÁNTICO #{i}\n")
            self.errores_sem_text.insert(tk.END, f"{'='*50}\n")
            self.errores_sem_text.insert(tk.END, f"📍 UBICACIÓN:\n")
            self.errores_sem_text.insert(tk.END, f"   Línea: {error.linea}\n")
            
            # Mostrar código de la línea si está disponible
            if isinstance(error.linea, int) and 1 <= error.linea <= len(lineas_codigo):
                codigo_linea = lineas_codigo[error.linea - 1].strip()
                if codigo_linea:
                    self.errores_sem_text.insert(tk.END, f"   Código: {codigo_linea}\n")
            
            self.errores_sem_text.insert(tk.END, f"\n🏷️  CLASIFICACIÓN:\n")
            self.errores_sem_text.insert(tk.END, f"   Tipo: {error.tipo}\n")
            
            self.errores_sem_text.insert(tk.END, f"\n📝 DESCRIPCIÓN:\n")
            self.errores_sem_text.insert(tk.END, f"   {error.descripcion}\n")
            
            self.errores_sem_text.insert(tk.END, f"\n📄 CONTEXTO:\n")
            self.errores_sem_text.insert(tk.END, f"   {error.contexto}\n")
            
            if error.sugerencia:
                self.errores_sem_text.insert(tk.END, f"\n💡 SUGERENCIA:\n")
                self.errores_sem_text.insert(tk.END, f"   {error.sugerencia}\n")
            
            self.errores_sem_text.insert(tk.END, f"\n{'='*50}\n\n")
    
    def actualizar_tabla(self):
        for item in self.tabla_tree.get_children():
            self.tabla_tree.delete(item)
        
        for simbolo in tabla_simbolos:
            self.tabla_tree.insert('', 'end', values=(
                simbolo.numero,
                simbolo.lexema,
                simbolo.token,
                simbolo.referencia or ''
            ))
    
    def limpiar_todo(self):
        global tabla_simbolos, contador_simbolos, errores, errores_semanticos, arboles_operaciones, lineas_codigo
        
        reiniciar_datos()
        
        self.actualizar_tabla()
        self.mensajes_text.delete('1.0', tk.END)
        self.errores_text.delete('1.0', tk.END)
        self.arbol_text.delete('1.0', tk.END)
        self.semantico_text.delete('1.0', tk.END)
        self.errores_sem_text.delete('1.0', tk.END)
        
        self.mensajes_text.insert(tk.END, "🗑️ Todos los datos han sido limpiados.\n")
    
    def cargar_archivo(self):
        file_path = filedialog.askopenfilename(
            title="Seleccionar archivo de código fuente",
            filetypes=[
                ("Archivos PF2024", "*.pf"),
                ("Archivos de texto", "*.txt"), 
                ("Todos los archivos", "*.*")
            ]
        )
        
        if file_path:
            try:
                with open(file_path, 'r', encoding='utf-8') as file:
                    contenido = file.read()
                    self.codigo_text.delete('1.0', tk.END)
                    self.codigo_text.insert('1.0', contenido)
                    self.mensajes_text.delete('1.0', tk.END)
                    self.mensajes_text.insert(tk.END, f"📁 Archivo cargado exitosamente: {file_path}\n")
            except Exception as e:
                self.mensajes_text.insert(tk.END, f"❌ Error al cargar el archivo: {str(e)}\n")

    def reiniciar_lexer(self):
        """Reinicia el lexer y su contador de líneas"""
        global analizador_lexico
        analizador_lexico.lineno = 1
        analizador_lexico.lexpos = 0

# ================= EJECUCIÓN PRINCIPAL =================
if __name__ == "__main__":
    print("="*70)
    print("ANALIZADOR SEMÁNTICO PF2024 - VERSIÓN COMPLETA")
    print("Incluye detección avanzada de errores semánticos")
    print("="*70)
    
    root = tk.Tk()
    app = AnalizadorGUI(root)
    root.mainloop()